-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_VerticalPointMultiplicityChart_length_localizedModule_quotient_377175effe8c
-- name    : P2M_GroundTheory_Heights__Heights_VerticalPointMultiplicityChart_length_localizedModule_quotient_377175effe8c
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T07:11:24.73309+00:00
-- url     : https://prove2.me/theorems/874e4b50-f423-56f4-8c28-8cb29436c795
-- title:
--   P2 M Ground Theory Heights  Heights Vertical Point Multiplicity Chart length localized Module quotient 377175effe8c: P2 M Ground Theory Heights  Heights Vertical Point Multiplicity Chart length locali
-- statement:
--   The P2 M Ground Theory Heights  Heights Vertical Point Multiplicity Chart length localized Module quotient 377175effe8c construction uses the P2 M Ground Theory Heights  Heights Vertical Point Multiplicity Chart length localized Module quotient 377175effe8c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PVertPointMultChart.lean#L14-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PVertPointMultChart.lean#L14-L24

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

theorem P2M_GroundTheory_Heights__Heights_VerticalPointMultiplicityChart_length_localizedModule_quotient_377175effe8c {R : Type*} [CommRing R] (p : Ideal R) [p.IsPrime] (I : Ideal R) :
    Module.length (Localization.AtPrime p) (LocalizedModule p.primeCompl (R ⧸ I)) =
      Module.length (Localization.AtPrime p)
        (Localization.AtPrime p ⧸ I.map (algebraMap R (Localization.AtPrime p))) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«VerticalPointMultiplicityChart».«length_localizedModule_quotient» := P2M_GroundTheory_Heights__Heights_VerticalPointMultiplicityChart_length_localizedModule_quotient_377175effe8c
