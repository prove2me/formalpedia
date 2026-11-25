-- Prove2me | Theorems.Thm_PI_WickFormula_Asm_xdeg_add
-- name    : PI.WickFormula.Asm.xdeg_add
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T08:44:42.583564+00:00
-- url     : https://prove2.me/theorems/e2d7dffa-6244-4efb-8d18-005b189e2a0c
-- title:
--   Asm: xdeg add
-- statement:
--   The Asm construction uses the xdeg add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/DiscriminantEstimates/DiscriminantLemmas/WickFormula/XdegLeTotalDegree.lean#L9-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/DiscriminantEstimates/DiscriminantLemmas/WickFormula/XdegLeTotalDegree.lean#L9-L10

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

theorem PI.WickFormula.Asm.xdeg_add {r s : ℕ} (u v : Fin r ⊕ Fin s →₀ ℕ) : xdeg (u + v) = xdeg u + xdeg v := by sorry
