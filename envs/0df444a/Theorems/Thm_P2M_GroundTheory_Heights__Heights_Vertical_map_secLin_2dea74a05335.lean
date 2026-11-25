-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_map_secLin_2dea74a05335
-- name    : P2M_GroundTheory_Heights__Heights_Vertical_map_secLin_2dea74a05335
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T04:43:52.402673+00:00
-- url     : https://prove2.me/theorems/c165dd88-0c98-4db0-a0bd-b14779bf4c67
-- title:
--   P2 M Ground Theory Heights  Heights Vertical map sec Lin 2dea74a05335: P2 M Ground Theory Heights  Heights Vertical map sec Lin 2dea74a05335
-- statement:
--   The P2 M Ground Theory Heights  Heights Vertical map sec Lin 2dea74a05335 construction uses the P2 M Ground Theory Heights  Heights Vertical map sec Lin 2dea74a05335 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PSecBLinInj.lean#L18-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PSecBLinInj.lean#L18-L30

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_IntToFracInjective
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PSecBLinInj
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Vertical
open MvPolynomial NumberField IsDedekindDomain
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_Vertical_map_secLin_2dea74a05335 {R S : Type*} [CommRing R] [CommRing S] {n e : ℕ}
    {Q : Ideal (MvPolynomial (Fin n) R)} {y : Par e n → R} {Q' : Ideal (MvPolynomial (Fin n) S)}
    {y' : Par e n → S} (ψ : SecAlg Q y →+* SecAlg Q' y') (c : R →+* S)
    (hc : ∀ j, ψ (secCoord Q y j) = secCoord Q' y' j)
    (hr : ∀ r : R, ψ (algebraMap R _ r) = algebraMap S _ (c r)) (w : Fin n → R) :
    ψ (secLin Q y w) = secLin Q' y' (fun j => c (w j)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Vertical».«map_secLin» := P2M_GroundTheory_Heights__Heights_Vertical_map_secLin_2dea74a05335
