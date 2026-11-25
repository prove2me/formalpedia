-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_ResBridge_D_null_d796392db77f
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_ResBridge_D_null_d796392db77f
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T16:28:08.575635+00:00
-- url     : https://prove2.me/theorems/34a7bc75-6274-4b0e-aece-8add1c0da300
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Res Bridge D null d796392db77f: P2 M Ground Theory Heights  Heights Hilbert Samuel Res Bridge D null d796392db77f
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Res Bridge D null d796392db77f construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Res Bridge D null d796392db77f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/ComponentResBadNullFlat.lean#L80-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/ComponentResBadNullFlat.lean#L80-L86

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_ComponentResBadNullLift
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_AnalyticSubsetChartLocal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeK
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_ComponentResBadNullFlat
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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel GroundTheory.Heights₂.Heights.HilbertSamuel.ResBridge
open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo Topology Filter Set
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {W : Ideal (MvPolynomial (Σ k, ι k) ℂ)} {e : ℕ} (R : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.Res ι W e)

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_ResBridge_D_null_d796392db77f (j : Fin R.atlas.n) :
    volume ((R.atlas.chart j).target ∩
      (R.atlas.chart j).symm ⁻¹' {x | R.pt x ∈ ReciprocityTheory.AnForm.R.conePts R.D}) = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«ResBridge».«D_null» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_ResBridge_D_null_d796392db77f
