-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowFormExtend_isChowForm_map_27b2fdc9a1f0
-- name    : P2M_GroundTheory_Heights__Heights_ChowFormExtend_isChowForm_map_27b2fdc9a1f0
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:57:48.852891+00:00
-- url     : https://prove2.me/theorems/d80b55e5-01ac-496a-af0b-6b2e042344d2
-- title:
--   P2 M Ground Theory Heights  Heights Chow Form Extend is Chow Form map 27b2fdc9a1f0: P2 M Ground Theory Heights  Heights Chow Form Extend is Chow Form map 27b2fdc9a1f0
-- statement:
--   The P2 M Ground Theory Heights  Heights Chow Form Extend is Chow Form map 27b2fdc9a1f0 construction uses the P2 M Ground Theory Heights  Heights Chow Form Extend is Chow Form map 27b2fdc9a1f0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PChowFormExtend.lean#L168-L215
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PChowFormExtend.lean#L168-L215

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

theorem P2M_GroundTheory_Heights__Heights_ChowFormExtend_isChowForm_map_27b2fdc9a1f0 (h : RadicalBaseChange.Statement) {K L : Type} [Field K] [PerfectField K]
    [Field L] [Algebra K L] {n k : ℕ} (I : Ideal (MvPolynomial (Fin n) K))
    (f : MvPolynomial (Fin k × Fin n) K) (hf : IsChowForm I k f) :
    IsChowForm (I.map (map (algebraMap K L))) k (map (algebraMap K L) f) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChowFormExtend».«isChowForm_map» := P2M_GroundTheory_Heights__Heights_ChowFormExtend_isChowForm_map_27b2fdc9a1f0
