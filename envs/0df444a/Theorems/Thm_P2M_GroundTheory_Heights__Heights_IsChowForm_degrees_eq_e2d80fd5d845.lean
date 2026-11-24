-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IsChowForm_degrees_eq_e2d80fd5d845
-- name    : P2M_GroundTheory_Heights__Heights_IsChowForm_degrees_eq_e2d80fd5d845
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T23:32:55.499203+00:00
-- url     : https://prove2.me/theorems/c3501a79-519a-4fbd-b372-031ebf098380
-- title:
--   P2 M Ground Theory Heights  Heights Is Chow Form degrees eq e2d80fd5d845: P2 M Ground Theory Heights  Heights Is Chow Form degrees eq e2d80fd5d845
-- statement:
--   The P2 M Ground Theory Heights  Heights Is Chow Form degrees eq e2d80fd5d845 construction uses the P2 M Ground Theory Heights  Heights Is Chow Form degrees eq e2d80fd5d845 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/ChowDegree.lean#L191-L209
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/ChowDegree.lean#L191-L209

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_RenameProdMapMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ChowDegree
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
variable {k n : ℕ}
variable {R : Type*} [CommRing R]
variable {F : Type} [Field F]

theorem P2M_GroundTheory_Heights__Heights_IsChowForm_degrees_eq_e2d80fd5d845 {I : Ideal (MvPolynomial (Fin n) F)} {g : MvPolynomial (Fin k × Fin n) F}
    (hg : IsChowForm I k g) {a : Fin k → ℕ} (ha : ∀ i, IsWeightedHomogeneous (inGroup i) g (a i))
    (i j : Fin k) : a i = a j := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IsChowForm».«degrees_eq» := P2M_GroundTheory_Heights__Heights_IsChowForm_degrees_eq_e2d80fd5d845
