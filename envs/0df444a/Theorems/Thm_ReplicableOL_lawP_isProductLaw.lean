-- Prove2me | Theorems.Thm_ReplicableOL_lawP_isProductLaw
-- name    : ReplicableOL.lawP_isProductLaw
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:49:42.236082+00:00
-- url     : https://prove2.me/theorems/be2bea42-8123-4cf3-be9b-d356fb1701c5
-- title:
--   Sec. 2.1, p.7 — each $P_\theta$ is a product law, and its bridge to bits
-- statement:
--   Fix $\Delta\in(0,1/4]$, an epoch length $L$ and a horizon $T$, and let $k=\lfloor T/L\rfloor$. For every $\theta\in[-\Delta,\Delta]^k$:
--
--   1. the law $P_\theta$ of Construction C is a product law on $([0,1]^2)^T$, with point masses on the trailing rounds;
--   2. for every measurable $f\ge0$,
--   $$
--   \int f\,dP_\theta=\sum_{b}\Big(\prod_{j\le k}\nu_{\mu_j}(b_j)\Big)f(\mathrm{embed}(b)),
--   $$
--   the sum being over all block sequences $b\in(\{0,1\}^L)^k$;
--   3. every adversarially $\rho$-replicable learner is $\rho$-replicable under $P_\theta$.
--
--   Moreover $\theta\mapsto P_\theta$ is measurable. This connects the measure-theoretic definition of replicability, which quantifies over product laws, with the finite sums used at a fixed seed.
--
--   Differences from the source:
--   - reading: one sentence: $P_\theta$ is a product law → the sentence plus the bridge to bits, the measurability of $\theta\mapsto P_\theta$, and the implication from adversarial replicability; reason: these are what the paper uses the sentence for (Lemma 2.3(b), p.8; the "in particular" of Theorem 1, p.9)
--   - encoding: losses in $[0,1]^2$ → `Fin 2 → ℝ`, with `IsProductLaw` requiring the factors to be carried by $[0,1]^2$; reason: Lean convention; same instances
-- source:
--   Lu, Replicable Online Learners Must Gamble: The Typical-Case Price of Replicability, STOC 2027 submission (held version, sha256 71ae0088…bbc2aa), Sec. 2.1, p.7

import Mathlib
import Definitions.Def_ReplicableOL_Learner
import Definitions.Def_ReplicableOL_IsProductLaw
import Definitions.Def_ReplicableOL_IsReplicableUnder
import Definitions.Def_ReplicableOL_IsAdvReplicable
import Definitions.Def_ReplicableOL_priorBox
import Definitions.Def_ReplicableOL_lawP
import Definitions.Def_ReplicableOL_Bits
import Definitions.Def_ReplicableOL_seqWeight
import Definitions.Def_ReplicableOL_embed
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace ReplicableOL

/-- **Sec. 2.1.** Lu, *Replicable Online Learners Must Gamble: The Typical-Case Price of Replicability*, STOC 2027 submission (held version), Sec. 2.1, p.7. "For each θ the law P_θ of S is a product law, with point masses on the trailing rounds."

**Formalization Note.** Three companions make the sentence usable: integrals under `lawP` are finite sums over bits, `θ ↦ lawP T L θ` is measurable (the kernel of Lemma 2.3(b)), and an adversarially ρ-replicable learner is ρ-replicable under each `lawP T L θ`, which is the "in particular" of Theorem 1 (p.9). -/
theorem lawP_isProductLaw {R : Type*} [MeasurableSpace R] {T L : ℕ} {Δ : ℝ} (hΔ : 0 < Δ) (hΔ' : Δ ≤ 1 / 4) :
    (∀ θ ∈ priorBox (T / L) Δ, IsProductLaw (lawP T L θ)) ∧
    (∀ θ ∈ priorBox (T / L) Δ, ∀ f : (Fin T → Fin 2 → ℝ) → ℝ≥0∞, Measurable f →
      ∫⁻ S, f S ∂(lawP T L θ) =
        ∑ b : Bits (T / L) L, ENNReal.ofReal (seqWeight θ b) * f (embed T (T / L) L b)) ∧
    Measurable (fun θ : Fin (T / L) → ℝ => lawP T L θ) ∧
    (∀ (𝓛 : Learner 2 T R) (PR : Measure R) (ρ : ℝ), IsAdvReplicable 𝓛 PR ρ →
      ∀ θ ∈ priorBox (T / L) Δ, IsReplicableUnder 𝓛 PR ρ (lawP T L θ)) := by sorry

end ReplicableOL
