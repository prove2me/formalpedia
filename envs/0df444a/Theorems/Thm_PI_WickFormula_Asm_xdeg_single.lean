-- Prove2me | Theorems.Thm_PI_WickFormula_Asm_xdeg_single
-- name    : PI.WickFormula.Asm.xdeg_single
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T08:45:54.064381+00:00
-- url     : https://prove2.me/theorems/351eda24-56ee-408d-b843-846023af520d
-- title:
--   Asm: xdeg single
-- statement:
--   The Asm construction uses the xdeg single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/DiscriminantEstimates/DiscriminantLemmas/WickFormula/XdegLeTotalDegree.lean#L12-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/DiscriminantEstimates/DiscriminantLemmas/WickFormula/XdegLeTotalDegree.lean#L12-L13

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

theorem PI.WickFormula.Asm.xdeg_single {r s : ℕ} (i : Fin r) : xdeg (Finsupp.single (Sum.inl i : Fin r ⊕ Fin s) 1) = 1 := by sorry
