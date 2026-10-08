-- Prove2me | Theorems.Thm_TDApprox_Conv_lemma_8
-- name    : TDApprox.Conv.lemma_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:50:54.477487+00:00
-- url     : https://prove2.me/theorems/b62be67f-9fc6-430a-9c31-6de43fa7900d
-- title:
--   Lemma 8, p. 17 — (r − r*)′E₀[s(r, X_t)] < 0 for every r ≠ r*
-- statement:
--   Under Assumptions 1 and 2, let $\lambda \in [0,1]$, let $r^*$ be the fixed point of Lemma 5, i.e. $\Pi T^{(\lambda)}(\Phi'r^*) = \Phi'r^*$, and let $X_t$ be the steady-state process of Lemma 7. Then
--   $$(r - r^*)'E_0[s(r,X_t)] < 0 \qquad \text{for every } r \ne r^*.$$
--
--   The expected TD($\lambda$) step points strictly towards $r^*$, so $r^*$ is the only candidate limit of the algorithm.
--
--   **Formalization Note.** $r^*$ enters as a hypothesis (any vector satisfying the fixed-point equation), which Lemma 5 shows exists and is unique.
-- source:
--   Tsitsiklis & Van Roy, LIDS-P-2322 (1996), Lemma 8, p. 17

import Mathlib
import Definitions.Def_TDApprox_Conv_Model
open MeasureTheory ProbabilityTheory Filter Topology Finset Matrix

namespace TDApprox.Conv

/-- **Lemma 8** (Tsitsiklis & Van Roy, LIDS-P-2322 (1996), p. 17). Under Assumptions 1 and 2, with
`λ ∈ [0, 1]` and `r*` the fixed point of Lemma 5 (`ΠT^(λ)(Φ′r*) = Φ′r*`),
`(r − r*)′E_0[s(r, X_t)] < 0` for every `r ≠ r*`. -/
theorem lemma_8 {S : Type*} [MeasurableSpace S] [DiscreteMeasurableSpace S] [Countable S]
    (P : Kernel S S) [IsMarkovKernel P] (π : Measure S) [IsProbabilityMeasure π]
    (g : S → S → ℝ) (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1)
    {K : ℕ} (φ : S → Fin K → ℝ)
    (h1 : Assumption1 P π g α) (h2 : Assumption2 π φ)
    (lam : ℝ) (hlam : lam ∈ Set.Icc (0 : ℝ) 1)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (i : ℤ → Ω → S) (hi : IsStationaryChain μ P π i)
    (rstar : Fin K → ℝ) (hfix : proj π φ (Tlam P g α lam (Jtilde φ rstar)) = Jtilde φ rstar) :
    ∀ (t : ℤ) (r : Fin K → ℝ), r ≠ rstar →
      (r - rstar) ⬝ᵥ (∫ ω, sStep α g φ r (Xstat α lam φ i t ω) ∂μ) < 0 := by sorry

end TDApprox.Conv
