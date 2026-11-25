-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_YPlusSupSmall_scale_e8aa871c45ea
-- name    : P2M_GroundTheory_Heights__Heights_YPlusSupSmall_scale_e8aa871c45ea
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T04:45:00.676582+00:00
-- url     : https://prove2.me/theorems/a5de0626-5412-49fe-a255-d13b64845564
-- title:
--   P2 M Ground Theory Heights  Heights YPlus Sup Small scale e8aa871c45ea: P2 M Ground Theory Heights  Heights YPlus Sup Small scale e8aa871c45ea
-- statement:
--   The P2 M Ground Theory Heights  Heights YPlus Sup Small scale e8aa871c45ea construction uses the P2 M Ground Theory Heights  Heights YPlus Sup Small scale e8aa871c45ea property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/PYPlusSupSmall.lean#L33-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/PYPlusSupSmall.lean#L33-L48

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

theorem P2M_GroundTheory_Heights__Heights_YPlusSupSmall_scale_e8aa871c45ea {R : Type*} [CommRing R] {τ : ℕ} {f : MvPolynomial (Coord D.extSizes) ℤ}
    (hf : Geo.IsMultiHomog (ι := blockIdx D.extSizes) f (Pi.single none τ)) (u w : Coord D.extSizes → R)
    (α β : R) (huw : ∀ j : Fin (D.size + 1), α * u ⟨none, j⟩ = β * w ⟨none, j⟩) :
    α ^ τ * aeval u f = β ^ τ * aeval w f := by sorry

alias «GroundTheory».«Heights₂».«Heights».«YPlusSupSmall».«scale» := P2M_GroundTheory_Heights__Heights_YPlusSupSmall_scale_e8aa871c45ea
