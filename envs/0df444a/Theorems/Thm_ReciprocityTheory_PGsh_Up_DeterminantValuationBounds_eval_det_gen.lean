-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_Up_DeterminantValuationBounds_eval_det_gen
-- name    : ReciprocityTheory.PGsh.Up.DeterminantValuationBounds.eval_det_gen
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T11:08:21.402092+00:00
-- url     : https://prove2.me/theorems/26f2b32d-d2cd-5437-847e-22d003efe4c2
-- title:
--   Determinant Valuation Bounds: eval det gen
-- statement:
--   The Determinant Valuation Bounds construction uses the eval det gen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/ValuationPairwiseDifferenceProductPowLeColengthS.lean#L82-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/ValuationPairwiseDifferenceProductPowLeColengthS.lean#L82-L90

import Definitions.Def_ReciprocityTheory_DualLattices_ColengthSqBlockVandermonde
import Definitions.Def_ReciprocityTheory_DualLattices_ValuationPairwiseDifferenceProductPowLeColengthS
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up
open ReciprocityTheory.PGsh.L2
open ReciprocityTheory.PGsh.Up.DeterminantValuationBounds
variable {C : Type} [Field C] {v : Valuation C NNReal}

theorem ReciprocityTheory.PGsh.Up.DeterminantValuationBounds.eval_det_gen {K : Type} [CommRing K] {ι σ : Type} [Fintype ι] [DecidableEq ι] [Fintype σ]
    (A : Matrix ι σ K) (z : σ × ι → K) :
    MvPolynomial.eval z (Matrix.det (Matrix.of fun i j =>
      ∑ r, MvPolynomial.C (A i r) * (MvPolynomial.X (r, j) : MvPolynomial (σ × ι) K))) =
      Matrix.det (Matrix.of fun i j => ∑ r, A i r * z (r, j)) := by sorry
