-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ObjectsChow_specFirst_eq_27ac14c10d3e
-- name    : P2M_GroundTheory_Heights__Heights_ObjectsChow_specFirst_eq_27ac14c10d3e
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:10:22.610769+00:00
-- url     : https://prove2.me/theorems/eafbb9ee-8fa8-4046-ac13-1868c4eb3ba1
-- title:
--   P2 M Ground Theory Heights  Heights Objects Chow spec First eq 27ac14c10d3e: P2 M Ground Theory Heights  Heights Objects Chow spec First eq 27ac14c10d3e
-- statement:
--   The P2 M Ground Theory Heights  Heights Objects Chow spec First eq 27ac14c10d3e construction uses the P2 M Ground Theory Heights  Heights Objects Chow spec First eq 27ac14c10d3e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/IsMultiHomogOfIsChowForm.lean#L31-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/IsMultiHomogOfIsChowForm.lean#L31-L34

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SpecFirstDetFormNeZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_IsMultiHomogOfIsChowForm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open GroundTheory.Heights₂.Heights.ObjectsChow
open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk Xc IsMultihomog)
variable {n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_ObjectsChow_specFirst_eq_27ac14c10d3e {R : Type*} [CommRing R] {e : ℕ} (f : MvPolynomial (Fin (e + 1) × Fin n) R)
    (u : Fin n → R) : specFirst f u = IndefiniteRowSideFullHecke.ArithBezout.specFirst u f := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ObjectsChow».«specFirst_eq» := P2M_GroundTheory_Heights__Heights_ObjectsChow_specFirst_eq_27ac14c10d3e
