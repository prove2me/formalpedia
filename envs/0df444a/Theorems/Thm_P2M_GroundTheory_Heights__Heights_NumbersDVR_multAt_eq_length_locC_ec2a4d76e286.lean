-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_multAt_eq_length_locC_ec2a4d76e286
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_multAt_eq_length_locC_ec2a4d76e286
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T04:13:40.590898+00:00
-- url     : https://prove2.me/theorems/b8739f31-5a5a-4602-9932-52badaa40236
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR mult At eq length loc C ec2a4d76e286: P2 M Ground Theory Heights  Heights Numbers DVR mult At eq length loc C ec2a4d76e286
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR mult At eq length loc C ec2a4d76e286 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR mult At eq length loc C ec2a4d76e286 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PDivCycleHomLoc.lean#L29-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PDivCycleHomLoc.lean#L29-L119

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsBlowUpFibreDegreeCut
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PDivCycleHomLocLaurent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PMinimalPrimeMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PCutByForm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PPolynomialLocalizedLength
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PDivCycleHomLoc
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial HomLocLaurent
noncomputable section
universe u
set_option linter.style.haveILetI false
variable {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type*} {R : Type*} [CommRing R]
  {P W : Ideal (MRing ι R)} [P.IsPrime] [W.IsPrime]

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_multAt_eq_length_locC_ec2a4d76e286 (hPW : P ≤ W) (x : MRing ι R) :
    multAt (P ⊔ Ideal.span {x}) W =
      Module.length (locC hPW) (locC hPW ⧸ Ideal.span {algQC hPW (Ideal.Quotient.mk P x)}) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«multAt_eq_length_locC» := P2M_GroundTheory_Heights__Heights_NumbersDVR_multAt_eq_length_locC_ec2a4d76e286
