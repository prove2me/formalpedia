-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P34_positive_reweighting
-- name    : QAlgorithms.Papers.Independent.Intake100.P34.positive_reweighting
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T18:13:32.992997+00:00
-- url     : https://prove2.me/theorems/be666e16-3526-4e7a-b6bd-a149c9f325bf
-- title:
--   Proposition 7.4 — positive reweighting preserves irreducibility
-- statement:
--   Let $d>0$, $n\ge1$, and let $\Phi_1,\ldots,\Phi_n$ be positive complex linear maps on $B(\mathbb C^d)$. If their sum is Davies irreducible and every real weight $\lambda_j$ is strictly positive, then
--
--   $$\sum_{j=1}^n\lambda_j\Phi_j\text{ is Davies irreducible}.$$
--
--   The weights need not be normalized. In dimension one this includes the harmless zero-map case. The result makes irreducibility stable under the positive weights introduced by deformation.
-- source:
--   Entropic fluctuations of quantum dynamical semigroups, arXiv:1305.4409v2, PDF p. 26, Proposition 7.4

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

/-- PDF p.26, Proposition 7.4: weights are strictly positive and need not sum to one. -/
theorem positive_reweighting {d n : ℕ} (hd : 0 < d) (hn : 0 < n)
    (Phi : Fin n → GeneratorMap d) (weights : Fin n → ℝ)
    (hPositive : ∀ j, IsPositiveMap (Phi j)) (hWeights : ∀ j, 0 < weights j)
    (hIrreducible : DaviesIrreducible (∑ j, Phi j)) :
    DaviesIrreducible (∑ j, (weights j : ℂ) • Phi j) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P34

end
