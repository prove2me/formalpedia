-- Prove2me | Theorems.Thm_StochAutoreg_Supplement_theorem_5_1
-- name    : StochAutoreg.Supplement.theorem_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T03:23:48.421053+00:00
-- url     : https://prove2.me/theorems/02091b56-7de7-414d-abe1-38e9a6eeea87
-- title:
--   Theorem 5.1 — $m^{\mathcal F,M}_{\mathrm{CoT}}(\varepsilon,\delta)\le m^{\mathcal F}_{\mathrm{base}}(\varepsilon/M,\delta)$, and the trajectory law is learned in KL
-- statement:
--   Let $\mathcal F$ be any class of generators, $M\ge1$, $\varepsilon>0$ and $0<\delta<1$. Then
--
--   $$m^{\mathcal F,M}_{\mathrm{CoT}}(\varepsilon,\delta)\le m^{\mathcal F}_{\mathrm{base}}(\varepsilon/M,\delta). \tag{5.1}$$
--
--   Moreover the reduction also learns the full conditional trajectory law in KL with accuracy $\varepsilon$: if $n=m^{\mathcal F}_{\mathrm{base}}(\varepsilon/M,\delta)$ is finite, there is a learner (measurable in its random seed) that, from $n$ i.i.d. chain-of-thought samples $(X_i,Z_{i,1},\dots,Z_{i,M})$, outputs a conditional law $\widehat Q(\cdot\mid x)$ on $\{0,1\}^M$ with
--
--   $$\mathbb E_{X\sim P}\,\mathrm{KL}\bigl(P^M_{g_\star}(\cdot\mid X)\,\|\,\widehat Q(\cdot\mid X)\bigr)\le\varepsilon$$
--
--   with probability at least $1-\delta$, for every target $g_\star\in\mathcal F$ and every prompt law $P$. Here $P^M_{g_\star}(\cdot\mid x)$ is the law of the $M$ generated tokens from the prompt $x$.
--
--   Learning one-step probabilities to accuracy $\varepsilon/M$ is thus always enough for chain-of-thought learning at accuracy $\varepsilon$, with no assumption on the class; Theorem 6.3 shows the accuracy $\varepsilon/M$ cannot be relaxed in general.
--
--   **Formalization Note** The KL divergence between laws on $\{0,1\}^M$ is Mathlib's `InformationTheory.klDiv`, valued in $[0,\infty]$, as in the published Proposition 4.2.
--
--   Differences from the source:
--   - encoding: sample complexities in {0,1,…,+∞} → ℕ∞, compared in ℕ∞; reason: the inequality (5.1) then also holds when either side is +∞
--   - reading: "The reduction also learns the full conditional trajectory law in KL with accuracy ε" (no sample size or confidence named) → with n = m_base(ε/M, δ) CoT samples (when finite), confidence 1 − δ, uniformly over g⋆ ∈ F and P, by a learner measurable in the seed; reason: the proof runs the same base learner at accuracy ε/M and confidence 1 − δ on the n reduced samples and bounds the trajectory KL by ε on its success event (5.2)
-- source:
--   Doron-Arad–Mehalel–Mossel, Stochastic Autoregressive Learning, arXiv:2608.07224, Theorem 5.1, p.11

import Mathlib
import Definitions.Def_StochAutoreg_mBase
import Definitions.Def_StochAutoreg_mCoT
import Definitions.Def_StochAutoreg_trajPMF
import Definitions.Def_StochAutoreg_cotLaw
import Definitions.Def_StochAutoreg_iidSeedMeasure
import Definitions.Def_StochAutoreg_promptMeasurableSpace

namespace StochAutoreg

namespace Supplement

/-- **Theorem 5.1** (from base to chain-of-thought supervision). For every class `F`, `M ≥ 1`, `ε > 0`
and `0 < δ < 1`, `m^{F,M}_CoT(ε, δ) ≤ m^F_base(ε/M, δ)` (Eq. (5.1)). The reduction also learns the
full conditional trajectory law in KL with accuracy `ε`.
Doron-Arad–Mehalel–Mossel, *Stochastic Autoregressive Learning*, arXiv:2608.07224, Theorem 5.1, Eq. (5.1), p.11.

**Formalization Note.** The complexities lie in `ℕ∞`, so (5.1) holds with `⊤` on either side. The
second clause: when `n = m^F_base(ε/M, δ)` is finite, a learner measurable in the seed outputs from
`n` i.i.d. CoT samples a conditional law `Q̂(·|x)` on `{0,1}^M` with
`E_{X∼P} KL(P^M_{g⋆}(·|X)‖Q̂(·|X)) ≤ ε` with probability at least `1 − δ`, for every `g⋆ ∈ F` and
every prompt law `P`. The KL between laws on `{0,1}^M` is `InformationTheory.klDiv` in `ℝ≥0∞`, as
in the published Proposition 4.2. -/
theorem theorem_5_1 (F : Set Generator) (M : ℕ) (hM : 1 ≤ M) (ε : ℝ) (hε : 0 < ε) (δ : ℝ)
    (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    mCoT F M ε δ ≤ mBase F (ε / M) δ ∧
    ∀ n : ℕ, mBase F (ε / M) δ = n →
      ∃ Qhat : (Fin n → List Bool × (Fin M → Bool)) → unitInterval → List Bool →
          PMF (Fin M → Bool),
        (∀ s x z, Measurable fun u => Qhat s u x z) ∧
        ∀ g ∈ F, ∀ P : PMF (List Bool),
          ENNReal.ofReal (1 - δ) ≤ iidSeedMeasure (cotLaw g M P) n
            {w | ∑' x, P x * InformationTheory.klDiv (trajPMF g M x).toMeasure
                (Qhat w.1 w.2 x).toMeasure ≤ ENNReal.ofReal ε} := by sorry

end Supplement

end StochAutoreg
