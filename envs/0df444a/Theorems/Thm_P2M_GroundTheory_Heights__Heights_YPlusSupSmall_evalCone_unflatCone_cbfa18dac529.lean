-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_YPlusSupSmall_evalCone_unflatCone_cbfa18dac529
-- name    : P2M_GroundTheory_Heights__Heights_YPlusSupSmall_evalCone_unflatCone_cbfa18dac529
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T04:43:51.163935+00:00
-- url     : https://prove2.me/theorems/1ab9c05e-13a9-41e6-b9a6-b9d75d16fec8
-- title:
--   P2 M Ground Theory Heights  Heights YPlus Sup Small eval Cone unflat Cone cbfa18dac529: P2 M Ground Theory Heights  Heights YPlus Sup Small eval Cone unflat Cone cbfa18dac529
-- statement:
--   The P2 M Ground Theory Heights  Heights YPlus Sup Small eval Cone unflat Cone cbfa18dac529 construction uses the P2 M Ground Theory Heights  Heights YPlus Sup Small eval Cone unflat Cone cbfa18dac529 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/PYPlusSupSmall.lean#L19-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/PYPlusSupSmall.lean#L19-L21

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_PYPlusSupSmall
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
open MvPolynomial ReciprocityTheory.ChartRestriction.G
noncomputable section
open GroundTheory.Heights₂.Heights.YPlusSupSmall
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ} {P : ArithVariety n} (D : AddBlockData P)

theorem P2M_GroundTheory_Heights__Heights_YPlusSupSmall_evalCone_unflatCone_cbfa18dac529 {κ : Type} {m : κ → ℕ} {R : Type*} [CommRing R] (w : Coord m → R)
    (p : MvPolynomial (Coord m) ℤ) : evalCone (unflatCone w) p = aeval w p := by sorry

alias «GroundTheory».«Heights₂».«Heights».«YPlusSupSmall».«evalCone_unflatCone» := P2M_GroundTheory_Heights__Heights_YPlusSupSmall_evalCone_unflatCone_cbfa18dac529
