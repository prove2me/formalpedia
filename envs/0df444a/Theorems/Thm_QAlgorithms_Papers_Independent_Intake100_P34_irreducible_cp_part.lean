-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P34_irreducible_cp_part
-- name    : QAlgorithms.Papers.Independent.Intake100.P34.irreducible_cp_part
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T18:04:21.391851+00:00
-- url     : https://prove2.me/theorems/d39eea18-9fbe-480e-93df-bdb5df9e8b49
-- title:
--   Theorem 2.3 — irreducible CP part implies positivity improvement
-- statement:
--   Let $d>0$, let $e^{tL}$ be a completely positive semigroup on $B(\mathbb C^d)$, and fix a decomposition $L(X)=K^*X+XK+\Phi(X)$ with $\Phi$ completely positive. If $\Phi$ is Davies irreducible, then
--
--   $$e^{tL}(X)>0\qquad(t>0,\ X\ge0,\ X\ne0).$$
--
--   The decomposition is specified, and neither unitality nor uniqueness of that decomposition is assumed. This is a usable criterion for positivity improvement.
-- source:
--   Entropic fluctuations of quantum dynamical semigroups, arXiv:1305.4409v2, PDF p. 5, Theorem 2.3

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

/-- PDF p.5, Theorem 2.3: the given CP part is irreducible; no unitality is assumed. -/
theorem irreducible_cp_part {d : ℕ} (hd : 0 < d) (L Phi : GeneratorMap d) (K : Mat d)
    (hCP : IsCPSemigroup L) (hPhi : QAlgorithms.Entanglement.IsCompletelyPositive Phi)
    (hDecomposition : ∀ X, L X = Kᴴ * X + X * K + Phi X)
    (hIrreducible : DaviesIrreducible Phi) :
    ∀ t : ℝ, 0 < t → IsImproving (qdsEvolution L t) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P34

end
