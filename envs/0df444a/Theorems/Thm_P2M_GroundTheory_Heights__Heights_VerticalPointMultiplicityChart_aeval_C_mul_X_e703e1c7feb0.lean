-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_VerticalPointMultiplicityChart_aeval_C_mul_X_e703e1c7feb0
-- name    : P2M_GroundTheory_Heights__Heights_VerticalPointMultiplicityChart_aeval_C_mul_X_e703e1c7feb0
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T07:39:19.941442+00:00
-- url     : https://prove2.me/theorems/353258fa-6b77-4ec2-83bf-b01877ead36c
-- title:
--   P2 M Ground Theory Heights  Heights Vertical Point Multiplicity Chart aeval C mul X e703e1c7feb0: P2 M Ground Theory Heights  Heights Vertical Point Multiplicity Chart aeval C mul X e703e1c7feb0
-- statement:
--   The P2 M Ground Theory Heights  Heights Vertical Point Multiplicity Chart aeval C mul X e703e1c7feb0 construction uses the P2 M Ground Theory Heights  Heights Vertical Point Multiplicity Chart aeval C mul X e703e1c7feb0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PVertPointMultChart.lean#L43-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PVertPointMultChart.lean#L43-L58

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsVertPointNagata
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PVertPointResidue
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PVertPointMultChart
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
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.VerticalPointMultiplicityChart

theorem P2M_GroundTheory_Heights__Heights_VerticalPointMultiplicityChart_aeval_C_mul_X_e703e1c7feb0 {T : Type} [Fintype T] {S : Type*} [CommRing S] (r : (Σ _ : Unit, T) → S)
    (f : MRing (fun _ : Unit => T)) (d : ℕ) (hf : IsMultiHomog f (fun _ => d)) :
    eval₂ (Int.castRingHom (Polynomial S)) (fun p => Polynomial.C (r p) * Polynomial.X) f =
      Polynomial.C (eval₂ (Int.castRingHom S) r f) * Polynomial.X ^ d := by sorry

alias «GroundTheory».«Heights₂».«Heights».«VerticalPointMultiplicityChart».«aeval_C_mul_X» := P2M_GroundTheory_Heights__Heights_VerticalPointMultiplicityChart_aeval_C_mul_X_e703e1c7feb0
