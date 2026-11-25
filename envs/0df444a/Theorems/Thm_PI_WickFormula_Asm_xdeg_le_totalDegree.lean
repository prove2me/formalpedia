-- Prove2me | Theorems.Thm_PI_WickFormula_Asm_xdeg_le_totalDegree
-- name    : PI.WickFormula.Asm.xdeg_le_totalDegree
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T08:44:18.909149+00:00
-- url     : https://prove2.me/theorems/65fe5574-299a-57f2-b826-0c17c4223405
-- title:
--   Asm: xdeg le total Degree
-- statement:
--   The Asm construction uses the xdeg le total Degree property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/DiscriminantEstimates/DiscriminantLemmas/WickFormula/XdegLeTotalDegree.lean#L15-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/DiscriminantEstimates/DiscriminantLemmas/WickFormula/XdegLeTotalDegree.lean#L15-L20

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

theorem PI.WickFormula.Asm.xdeg_le_totalDegree {k : Type} [CommRing k] {r s : ℕ} (P : MvPolynomial (Fin r ⊕ Fin s) k)
    (m : Fin r ⊕ Fin s →₀ ℕ) (hm : m ∈ P.support) : xdeg m ≤ P.totalDegree := by sorry
