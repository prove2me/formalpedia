-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowFormExtend_radical_map_eq_9ece7ec07417
-- name    : P2M_GroundTheory_Heights__Heights_ChowFormExtend_radical_map_eq_9ece7ec07417
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:56:26.705573+00:00
-- url     : https://prove2.me/theorems/4482e0ba-0717-4568-aece-f22c6180f7e0
-- title:
--   P2 M Ground Theory Heights  Heights Chow Form Extend radical map eq 9ece7ec07417: P2 M Ground Theory Heights  Heights Chow Form Extend radical map eq 9ece7ec07417
-- statement:
--   The P2 M Ground Theory Heights  Heights Chow Form Extend radical map eq 9ece7ec07417 construction uses the P2 M Ground Theory Heights  Heights Chow Form Extend radical map eq 9ece7ec07417 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PChowFormExtend.lean#L69-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PChowFormExtend.lean#L69-L75

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsBaseChange
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PChowFormExtend
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.ChowFormExtend
variable {F : Type*} [Field F] {n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_ChowFormExtend_radical_map_eq_9ece7ec07417 (h : RadicalBaseChange.Statement) {K L : Type} [Field K] [PerfectField K]
    [Field L] (σ : K →+* L) {ι : Type} (J : Ideal (MvPolynomial ι K)) :
    (J.map (MvPolynomial.map σ)).radical = J.radical.map (MvPolynomial.map σ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChowFormExtend».«radical_map_eq» := P2M_GroundTheory_Heights__Heights_ChowFormExtend_radical_map_eq_9ece7ec07417
