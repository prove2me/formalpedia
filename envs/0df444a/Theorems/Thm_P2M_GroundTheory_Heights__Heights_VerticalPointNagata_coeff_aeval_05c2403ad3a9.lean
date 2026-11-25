-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_VerticalPointNagata_coeff_aeval_05c2403ad3a9
-- name    : P2M_GroundTheory_Heights__Heights_VerticalPointNagata_coeff_aeval_05c2403ad3a9
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T08:06:45.700688+00:00
-- url     : https://prove2.me/theorems/eb9293d2-8f6f-44cf-9a78-a618703afcbd
-- title:
--   P2 M Ground Theory Heights  Heights Vertical Point Nagata coeff aeval 05c2403ad3a9: P2 M Ground Theory Heights  Heights Vertical Point Nagata coeff aeval 05c2403ad3a9
-- statement:
--   The P2 M Ground Theory Heights  Heights Vertical Point Nagata coeff aeval 05c2403ad3a9 construction uses the P2 M Ground Theory Heights  Heights Vertical Point Nagata coeff aeval 05c2403ad3a9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PVertPointNagata.lean#L47-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PVertPointNagata.lean#L47-L63

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsVertPointNagata
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PVertPointMultChart
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PLocRingPow
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PVertPointNagata
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
open GroundTheory.Heights₂.Heights.VerticalPointNagata
variable {T : Type} [Fintype T]

theorem P2M_GroundTheory_Heights__Heights_VerticalPointNagata_coeff_aeval_05c2403ad3a9 {S : Type*} [CommRing S] [Algebra ℤ S] [Algebra ℤ (Polynomial S)] (r : (Σ _ : Unit, T) → S) (f : MRing (fun _ : Unit => T))
    (n : ℕ) :
    (aeval (fun p => Polynomial.C (r p) * Polynomial.X) f : Polynomial S).coeff n = aeval r (comp n f) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«VerticalPointNagata».«coeff_aeval» := P2M_GroundTheory_Heights__Heights_VerticalPointNagata_coeff_aeval_05c2403ad3a9
