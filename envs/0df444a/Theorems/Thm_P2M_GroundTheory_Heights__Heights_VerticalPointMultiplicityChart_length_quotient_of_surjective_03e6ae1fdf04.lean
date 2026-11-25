-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_VerticalPointMultiplicityChart_length_quotient_of_surjective_03e6ae1fdf04
-- name    : P2M_GroundTheory_Heights__Heights_VerticalPointMultiplicityChart_length_quotient_of_surjective_03e6ae1fdf04
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T07:12:14.214241+00:00
-- url     : https://prove2.me/theorems/338fbe59-e8cb-5ab8-b41b-ef4fb8ba3da9
-- title:
--   P2 M Ground Theory Heights  Heights Vertical Point Multiplicity Chart length quotient of surjective 03e6ae1fdf04: P2 M Ground Theory Heights  Heights Vertical Point Multiplicity Chart length quotient
-- statement:
--   The P2 M Ground Theory Heights  Heights Vertical Point Multiplicity Chart length quotient of surjective 03e6ae1fdf04 construction uses the P2 M Ground Theory Heights  Heights Vertical Point Multiplicity Chart length quotient of surjective 03e6ae1fdf04 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PVertPointMultChart.lean#L26-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PVertPointMultChart.lean#L26-L41

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

theorem P2M_GroundTheory_Heights__Heights_VerticalPointMultiplicityChart_length_quotient_of_surjective_03e6ae1fdf04 {A N : Type*} [CommRing A] [CommRing N] (Φ : A →+* N)
    (hΦ : Function.Surjective Φ) (J : Ideal A) (hJ : RingHom.ker Φ ≤ J) :
    Module.length A (A ⧸ J) = Module.length N (N ⧸ J.map Φ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«VerticalPointMultiplicityChart».«length_quotient_of_surjective» := P2M_GroundTheory_Heights__Heights_VerticalPointMultiplicityChart_length_quotient_of_surjective_03e6ae1fdf04
