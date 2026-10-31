-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P34_chaotic_finite_time_ES
-- name    : QAlgorithms.Papers.Independent.Intake100.P34.chaotic_finite_time_ES
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T18:14:26.700271+00:00
-- url     : https://prove2.me/theorems/847c6733-d371-41cd-ad93-d12cccc7c1ca
-- title:
--   §3.2 Remark 1 — chaotic-state finite-time symmetry
-- statement:
--   Let $L=\sum_jL_j$ be a detailed-balance QDS on $B(\mathbb C^d)$, $d>0$, whose reservoir pairs share a time reversal. For the chaotic density $\rho_{\mathrm{ch}}=1/d$, define $e_{\rho,t}(\alpha)=\log\operatorname{tr}(\rho e^{tL_{(\alpha)}}(1))$. Then
--
--   $$e_{\rho_{\mathrm{ch}},t}(1-\alpha)=e_{\rho_{\mathrm{ch}},t}(\alpha)\qquad(t\ge0,\ \alpha\in\mathbb R^M).$$
--
--   No ergodicity hypothesis is imposed. This is the source's exceptional finite-time symmetry for the specified initial state.
-- source:
--   Entropic fluctuations of quantum dynamical semigroups, arXiv:1305.4409v2, PDF p. 7, §3.2 Remark 1

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P34

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ENNReal NNReal Matrix.Norms.L2Operator ComplexOrder

open MeasureTheory Filter

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Intake100.P34

open QAlgorithms (IsDensityMatrix)

open QAlgorithms.Papers.Independent.Dependency50.P16 (sandwich)

open QAlgorithms.Papers.Independent.Information100.P26 (Mat commutant scalars)

open QAlgorithms.Papers.Independent.Information100.P30 (MatrixMap IsPositiveMap)

open QAlgorithms.Papers.Independent.Information100.P56 (entropy)

open QAlgorithms.Papers.Independent.Information100.P69 (Faithful)

open QAlgorithms.Papers.Independent.Bridge50.P37 (hsAdjoint)

open QAlgorithms.Papers.Independent.Claimed50.P15
  (evaluate finiteRelativeEntropyNats entropyObservable)

open QAlgorithms.Papers.Independent.Claimed50.P43 (chaotic)

/-- PDF p.3: complex linear superoperators. -/
local notation "GeneratorMap" => fun d : ℕ => MatrixMap (Fin d) (Fin d)

/-- PDF p.7, Remark 1: the exceptional finite-time ES identity is for the chaotic state.
ER is not required. -/
theorem chaotic_finite_time_ES {d M : ℕ} (D : DBData d M) (hTR : TR D) :
    ∀ t : ℝ, 0 ≤ t → ∀ a : EntropyCoordinates M,
      finiteCGF D (chaotic d) t (fun j => 1 - a j) = finiteCGF D (chaotic d) t a := by sorry

end QAlgorithms.Papers.Independent.Intake100.P34

end
