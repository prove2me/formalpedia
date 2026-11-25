-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_VerticalPointNagata_aeval_C_mul_X__435eef58e544
-- name    : P2M_GroundTheory_Heights__Heights_VerticalPointNagata_aeval_C_mul_X__435eef58e544
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T07:11:39.339706+00:00
-- url     : https://prove2.me/theorems/42f52674-6578-5616-aef3-2912819d7bc8
-- title:
--   P2 M Ground Theory Heights  Heights Vertical Point Nagata aeval C mul X  435eef58e544: P2 M Ground Theory Heights  Heights Vertical Point Nagata aeval C mul X  435eef58e544
-- statement:
--   The P2 M Ground Theory Heights  Heights Vertical Point Nagata aeval C mul X  435eef58e544 construction uses the P2 M Ground Theory Heights  Heights Vertical Point Nagata aeval C mul X  435eef58e544 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PVertPointNagata.lean#L41-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PVertPointNagata.lean#L41-L45

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

theorem P2M_GroundTheory_Heights__Heights_VerticalPointNagata_aeval_C_mul_X__435eef58e544 {S : Type*} [CommRing S] [Algebra ℤ S] [Algebra ℤ (Polynomial S)] (r : (Σ _ : Unit, T) → S)
    (f : MRing (fun _ : Unit => T)) (d : ℕ) (hf : IsMultiHomog f (fun _ => d)) :
    (aeval (fun p => Polynomial.C (r p) * Polynomial.X) f : Polynomial S) =
      Polynomial.C (aeval r f) * Polynomial.X ^ d := by sorry

alias «GroundTheory».«Heights₂».«Heights».«VerticalPointNagata».«aeval_C_mul_X'» := P2M_GroundTheory_Heights__Heights_VerticalPointNagata_aeval_C_mul_X__435eef58e544
