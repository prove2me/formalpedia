-- Prove2me | Theorems.Thm_PI_WickFormula_Asm_ordEval_zero
-- name    : PI.WickFormula.Asm.ordEval_zero
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T08:44:35.733102+00:00
-- url     : https://prove2.me/theorems/98745611-2d64-4b2c-970e-30f2c00bf96f
-- title:
--   Asm: ord Eval zero
-- statement:
--   The Asm construction uses the ord Eval zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/DiscriminantEstimates/DiscriminantLemmas/WickFormula/XdegLeTotalDegree.lean#L45-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/DiscriminantEstimates/DiscriminantLemmas/WickFormula/XdegLeTotalDegree.lean#L45-L48

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantLemmas_WickFormula_DeltaEqGdelta
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantLemmas_WickFormula_XdegLeTotalDegree
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open PI PI.WickFormula PI.WickFormula.Asm
variable {k AA M : Type} [CommRing k] [Algebra ℚ k] [Ring AA] [Algebra k AA] [AddCommGroup M]
  [Module AA M] {r s : ℕ}

theorem PI.WickFormula.Asm.ordEval_zero (h1 : OrdLin) (a : Fin r → AA) (a' : Fin s → AA) :
    ordEval a a' (0 : MvPolynomial (Fin r ⊕ Fin s) k) = 0 := by sorry
