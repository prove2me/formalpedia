-- Prove2me | Theorems.Thm_ReplicableOL_lemma_2_3
-- name    : ReplicableOL.lemma_2_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:49:22.655538+00:00
-- url     : https://prove2.me/theorems/d8bdf682-1161-4568-83c2-16c78087bb28
-- title:
--   Lemma 2.3 — canonical trajectories
-- statement:
--   For a finite set $Z$, a jointly measurable $F(S,r)\in Z$ and a law $Q$ of $S$, let $\varepsilon_F(Q,r)=1-\max_z\mathbb P_{S\sim Q}[F(S,r)=z]$, let $\rho_F(Q,r)=\mathbb P_{S,S'\sim Q}[F(S,r)\ne F(S',r)]$, and let $z^\star_F(Q,r)$ be the least maximizer in a fixed order on $Z$. The canonical prefix is $\tau^\star_{\le t}(Q,r)=z^\star_{\tau_{\le t}}(Q,r)$.
--
--   (a) For every $F,Q,r$:
--   $$
--   \varepsilon_F(Q,r)\le\rho_F(Q,r)\le2\varepsilon_F(Q,r).
--   $$
--   If the learner is $\rho$-replicable under $P$, then for every $t$ and $\eta\in(0,1]$,
--   $$
--   P_R\big[P_S(\tau_{\le t}(S,R)\ne\tau^\star_{\le t}(P,R))\ge\eta\big]\le\rho/\eta.
--   $$
--
--   (b) If $\theta\sim\pi$, $\theta\mapsto P_\theta$ is a probability kernel and the learner is $\rho$-replicable under every $P_\theta$, then $\rho^\pi(r):=\mathbb E_\theta\rho_\tau(P_\theta,r)$ satisfies $\mathbb E_R\rho^\pi(R)\le\rho$.
--
--   Part (b) is the only way the main theorem uses replicability.
--
--   Differences from the source:
--   - generalization: the learner is adversarially $\rho$-replicable and $P$, $P_\theta$ are product laws → $\rho$-replicable under the law $P$ (part (a)), and under $\pi$-a.e. $\kappa(\theta)$ (part (b)), with $\kappa$ a.e. a probability measure; reason: adversarial replicability gives these hypotheses for product laws; p.8: "(b) holds for every learner that is $\rho$-replicable under each $P_\theta$"
--   - encoding: a fixed order on $Z$ → a `LinearOrder` instance on each `Fin t → Fin n`; reason: the statement holds for each order, which is what "a fixed order" leaves open
--   - encoding: $\tau_{\le t}$ for $t\le T$ → `trajPrefix 𝓛 t` with `t : Fin (T + 1)`; reason: same prefixes, $t=0$ included
--   - generalization: laws $Q,P$ of $S$ on $([0,1]^n)^T$ and $F$ on $([0,1]^n)^T\times\mathcal R$ → probability measures on `Fin T → Fin n → ℝ` and `F` on all real loss sequences; reason: the proof (p.11) uses only that $Q$ is a probability law and $F$ is jointly measurable; a page $F$ extends measurably off $[0,1]^n$
--   - encoding: a learner whose maps $a_t$ read $[0,1]$-valued losses → `Learner` with maps on all real loss vectors (`Fin t → Fin 2 → ℝ`); reason: a learner on $[0,1]$ extends measurably to $\mathbb R$ and a `Learner` restricts to $[0,1]$; every law and every `embed` sequence here is carried by $[0,1]^2$
-- source:
--   Lu, Replicable Online Learners Must Gamble: The Typical-Case Price of Replicability, STOC 2027 submission (held version, sha256 71ae0088…bbc2aa), Lemma 2.3, p.8

import Mathlib
import Definitions.Def_ReplicableOL_Learner
import Definitions.Def_ReplicableOL_trajPrefix
import Definitions.Def_ReplicableOL_disagreeProb
import Definitions.Def_ReplicableOL_IsReplicableUnder
import Definitions.Def_ReplicableOL_modeDefect
import Definitions.Def_ReplicableOL_outputDisagree
import Definitions.Def_ReplicableOL_canonical
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace ReplicableOL

/-- **Lemma 2.3.** Lu, *Replicable Online Learners Must Gamble: The Typical-Case Price of Replicability*, STOC 2027 submission (held version), Lemma 2.3, p.8. Parts (a) and (b).

**Formalization Note.** Part (a), second claim, and part (b) take ρ-replicability under the law in question; the page says (b) holds in this form, and (a) uses only that. "A fixed order" on prefixes is an arbitrary `LinearOrder` family, passed as an instance. Part (b) takes any kernel `κ` that is a.e. a probability measure, so that it applies to `lawP`, which is a probability measure on the prior's support. -/
theorem lemma_2_3 {n T : ℕ} [NeZero n] {R Z Θ : Type*} [MeasurableSpace R] [Fintype Z] [Nonempty Z]
    [MeasurableSpace Z] [MeasurableSingletonClass Z] [MeasurableSpace Θ]
    [∀ t : ℕ, LinearOrder (Fin t → Fin n)] :
    (∀ F : (Fin T → Fin n → ℝ) → R → Z, Measurable (Function.uncurry F) →
      ∀ (Q : Measure (Fin T → Fin n → ℝ)) [IsProbabilityMeasure Q] (r : R),
        modeDefect F Q r ≤ outputDisagree F Q r ∧ outputDisagree F Q r ≤ 2 * modeDefect F Q r) ∧
    (∀ (PR : Measure R) [IsProbabilityMeasure PR] (𝓛 : Learner n T R) (ρ : ℝ)
        (P : Measure (Fin T → Fin n → ℝ)) [IsProbabilityMeasure P],
      IsReplicableUnder 𝓛 PR ρ P →
      ∀ (t : Fin (T + 1)) (η : ℝ), 0 < η → η ≤ 1 →
        PR {r | ENNReal.ofReal η ≤ P {S | trajPrefix 𝓛 t S r ≠ canonical (trajPrefix 𝓛 t) P r}} ≤
          ENNReal.ofReal (ρ / η)) ∧
    (∀ (PR : Measure R) [IsProbabilityMeasure PR] (𝓛 : Learner n T R) (ρ : ℝ)
        (π : Measure Θ) [IsProbabilityMeasure π] (κ : Θ → Measure (Fin T → Fin n → ℝ)),
      Measurable κ →
      (∀ᵐ θ ∂π, IsProbabilityMeasure (κ θ) ∧ IsReplicableUnder 𝓛 PR ρ (κ θ)) →
      ∫⁻ r, ∫⁻ θ, disagreeProb 𝓛 (κ θ) r ∂π ∂PR ≤ ENNReal.ofReal ρ) := by sorry

end ReplicableOL
