-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P34_irreducible_exponential
-- name    : QAlgorithms.Papers.Independent.Intake100.P34.irreducible_exponential
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T18:12:42.658948+00:00
-- url     : https://prove2.me/theorems/c84a6142-048d-44e1-8d8e-31c3464d22f9
-- title:
--   Proposition 7.3 — irreducibility and exponential positivity
-- statement:
--   Let $\Phi$ be a positive complex linear map on $B(\mathbb C^d)$, $d>0$. Then
--
--   $$\Phi\text{ is Davies irreducible}\quad\Longleftrightarrow\quad e^{t\Phi}\text{ is positivity improving for some }t>0\quad\Longleftrightarrow\quad e^{t\Phi}\text{ is positivity improving for every }t>0.$$
--
--   Complete positivity and normalization are unnecessary. This characterizes irreducibility through the genuine operator exponential.
-- source:
--   Entropic fluctuations of quantum dynamical semigroups, arXiv:1305.4409v2, PDF p. 24, Proposition 7.3

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

/-- PDF pp.24–25, Proposition 7.3: positivity suffices, with both the some-time and all-time clauses. -/
theorem irreducible_exponential {d : ℕ} (hd : 0 < d) (Phi : GeneratorMap d) (hPositive : IsPositiveMap Phi) :
    (DaviesIrreducible Phi ↔ ∃ t : ℝ, 0 < t ∧ IsImproving (qdsEvolution Phi t)) ∧
    (DaviesIrreducible Phi ↔ ∀ t : ℝ, 0 < t → IsImproving (qdsEvolution Phi t)) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P34

end
