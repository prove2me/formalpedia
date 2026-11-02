-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P95_pptCatalysis
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P95.pptCatalysis
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T09:38:32.966667+00:00
-- url     : https://prove2.me/theorems/4d8068b0-e39c-4c53-9457-eb4c1b334500
-- title:
--   Abstract and Section IV: PPT catalysis exists with a maximally entangled catalyst
-- statement:
--   All logarithms have base two. A PPT operation is a completely positive, trace-preserving map $L$ such that $\Gamma_{\rm out}L\Gamma_{\rm in}$ is completely positive for arbitrary finite ancillary systems; $\Gamma$ transposes Bob in the fixed product basis. For a positive integer $K$, $\Phi_K$ denotes the maximally entangled state of Schmidt rank $K$. There exists a strictly positive three-entry probability vector $\lambda$ for which
--
--   $$\Phi_2\not\to^{\rm PPT}\rho_\lambda,\qquad\exists C\ge2:\;\Phi_C\otimes\Phi_2\to^{\rm PPT}\Phi_C\otimes\rho_\lambda.$$
--
--   Hence PPT catalysis occurs even when the catalyst is maximally entangled, as asserted in the abstract and Section IV.
-- source:
--   Pure-state transformations and catalysis under operations that completely preserve positivity of partial transpose, arXiv:0801.4322v2, PDF p. 1, Abstract and Section IV: PPT catalysis exists with a maximally entangled catalyst

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P95

noncomputable section

open scoped BigOperators Matrix ComplexOrder

open Filter

namespace QAlgorithms.Papers.Independent.Intakethird100.P95

attribute [local instance] Classical.propDecidable Classical.decEq

-- Exact primitives from the pinned accepted library; no local aliases.

open QAlgorithms.Papers.Independent.Claimed50.P28 (maximallyEntangledDensity)

open QAlgorithms.Papers.Independent.Information100.P27 (IsProbability)

open QAlgorithms.Papers.Independent.Information100.P63 (logTwo)

open QAlgorithms.Papers.Independent.Information100.P19 (outer)

open QAlgorithms.Papers.Independent.Dependency50.P18 (bipartiteTensor)

open QAlgorithms.Papers.Independent.Support50.P11 (Loewner)

/-- PDF pp.1,9–10: PPT catalysis exists, even with a maximally entangled catalyst.
Figure 1 and the strict inclusion following (51) identify an EPR input and rank-three target. -/
theorem pptCatalysis :
    ∃ lam : Fin 3 → ℝ, IsProbability lam ∧ (∀ i, 0 < lam i) ∧
      ¬ Reach (maximallyEntangledDensity 2) (schmidtDensity lam) ∧ CatalyticPreparation 2 lam := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P95

end
