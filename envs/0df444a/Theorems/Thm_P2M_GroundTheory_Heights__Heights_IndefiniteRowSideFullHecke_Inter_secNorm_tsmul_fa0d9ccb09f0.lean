-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_secNorm_tsmul_fa0d9ccb09f0
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_secNorm_tsmul_fa0d9ccb09f0
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T15:51:28.106308+00:00
-- url     : https://prove2.me/theorems/0f987efe-1473-4472-9866-80f36c893b3e
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter sec Norm tsmul fa0d9ccb09f0: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter sec Norm tsmul fa0d9ccb09
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter sec Norm tsmul fa0d9ccb09f0 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter sec Norm tsmul fa0d9ccb09f0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/FourierIntegralBound.lean#L43-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/FourierIntegralBound.lean#L43-L56

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_AnalyticResolutionHypothesesProjectiveLine
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeN
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_LocDens
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_FourierIntegralBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
open MvPolynomial MeasureTheory Topology Filter Set
open scoped ContDiff
open GroundTheory.Heights₂.Heights.NumbersDVR (MRing IsMultiHomog)
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential MIntegrable locDens)
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_secNorm_tsmul_fa0d9ccb09f0 {P : Ideal (MRing ι ℂ)} {A : HLine ι} {s : MRing ι ℂ} (hs : IsFormSec P A s)
    {c : K → ℂ} (hc : ∀ k, c k ≠ 0) (z : MCone ι) :
    secNorm A s (tsmul c z) = secNorm A s z := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Inter».«secNorm_tsmul» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_secNorm_tsmul_fa0d9ccb09f0
