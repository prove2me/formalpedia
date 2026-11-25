-- Prove2me | Theorems.Thm_P2M_RH_ReciprocityTheory_AnForm_R_ptIdeal_isMaximal_a3d235ebb1deb6ff
-- name    : P2M_RH_ReciprocityTheory_AnForm_R_ptIdeal_isMaximal_a3d235ebb1deb6ff
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T05:12:19.347547+00:00
-- url     : https://prove2.me/theorems/f7d88142-e5ab-4a0f-9151-7a6276e375ce
-- title:
--   P2 M RH Reciprocity Theory An Form R pt Ideal is Maximal a3d235ebb1deb6ff: P2 M RH Reciprocity Theory An Form R pt Ideal is Maximal a3d235ebb1deb6ff
-- statement:
--   The P2 M RH Reciprocity Theory An Form R pt Ideal is Maximal a3d235ebb1deb6ff construction uses the P2 M RH Reciprocity Theory An Form R pt Ideal is Maximal a3d235ebb1deb6ff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/RingKrullDimLocRingEqOfMinimalPrime.lean#L12-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/RingKrullDimLocRingEqOfMinimalPrime.lean#L12-L13

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_JacChart
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_PolynomialHeights_HeightAddRingKrullDimQuotientMvPolynomialField
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_MaximalIdealSquares_RingKrullDimQuotientSpanSingletonAddOne
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_RingKrullDimLocRingEqOfMinimalPrime
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R
open MvPolynomial
variable {n : ℕ}

theorem P2M_RH_ReciprocityTheory_AnForm_R_ptIdeal_isMaximal_a3d235ebb1deb6ff (p : Fin n → ℂ) : (ptIdeal p).IsMaximal := by sorry

alias «ReciprocityTheory».«AnForm».«R».«ptIdeal_isMaximal» := P2M_RH_ReciprocityTheory_AnForm_R_ptIdeal_isMaximal_a3d235ebb1deb6ff
