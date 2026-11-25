-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_bijective_smul_of_isHomogeneous_7a9bef9a2abe
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_bijective_smul_of_isHomogeneous_7a9bef9a2abe
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T08:50:22.510807+00:00
-- url     : https://prove2.me/theorems/0be7ac07-7e1e-49df-94a0-62d237a4dff1
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman bijective smul of is Homogeneous 7a9bef9a2abe: P2 M Ground Theory Heights  Heights Kleiman bijective smul of is Homogeneous 7a9bef9a2abe
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman bijective smul of is Homogeneous 7a9bef9a2abe construction uses the P2 M Ground Theory Heights  Heights Kleiman bijective smul of is Homogeneous 7a9bef9a2abe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PTildeVanishCone.lean#L114-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PTildeVanishCone.lean#L114-L123

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_AlgebraMapMemChartRingLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PTildeTailLoc
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PTildeVanishCone
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u v w
variable (S : Type u) [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  (x : Fin (N + 1) → Ω) (E : Type v) [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]
variable {S x E}
variable (S x E)
variable {S x E}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_bijective_smul_of_isHomogeneous_7a9bef9a2abe {s : Poly S N} {e : ℕ} (hs : s.IsHomogeneous e)
    (h0 : aeval x s ≠ 0) : Function.Bijective (fun w : ConeE S x E => s • w) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«bijective_smul_of_isHomogeneous» := P2M_GroundTheory_Heights__Heights_Kleiman_bijective_smul_of_isHomogeneous_7a9bef9a2abe
