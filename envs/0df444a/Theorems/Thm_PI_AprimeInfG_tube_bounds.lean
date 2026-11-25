-- Prove2me | Theorems.Thm_PI_AprimeInfG_tube_bounds
-- name    : PI.AprimeInfG.tube_bounds
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T08:13:47.233412+00:00
-- url     : https://prove2.me/theorems/73e03c64-94d9-4925-ac7b-e4d7df8304c0
-- title:
--   Aprime Inf G: tube bounds
-- statement:
--   The Aprime Inf G construction uses the tube bounds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ArchimedeanOrbitMeasures/GrpTube.lean#L111-L230
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ArchimedeanOrbitMeasures/GrpTube.lean#L111-L230

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_LintegralMulRightOfMem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_GrpTube
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.AprimeInfG
open MeasureTheory Topology Filter Metric Set
open scoped ENNReal
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

theorem PI.AprimeInfG.tube_bounds (μ : Measure G) [μ.IsHaarMeasure] (H : Subgroup G) (ν : Measure H) [ν.IsMulLeftInvariant]
    [SFinite ν] (hν0 : ν univ ≠ 0) (hνf : ν univ ≠ ∞) {ι η : Type} [Fintype ι] [Fintype η]
    {κ : EuclideanSpace ℝ ι → G} {χ : EuclideanSpace ℝ η → H} {r0 : ℝ} {d : EuclideanSpace ℝ ι × EuclideanSpace ℝ η → ℝ}
    {e : EuclideanSpace ℝ η → ℝ} (hC : TubeChart μ H ν κ χ r0 d e)
    {ε s ρ : ℝ} (hε : 0 < ε) (hεd : ε < d 0) (hεe : ε < e 0) (hs : 0 < s) (hsr : s ≤ r0) (hρ : 0 < ρ)
    (hρs : ρ ≤ s) (hdε : ∀ p : EuclideanSpace ℝ ι × EuclideanSpace ℝ η, ‖p‖ < s → |d p - d 0| < ε)
    (heε : ∀ y : EuclideanSpace ℝ η, ‖y‖ < s → |e y - e 0| < ε) :
    0 < μ (tubeS H (κ '' ball 0 ρ) univ) ∧ μ (tubeS H (κ '' ball 0 ρ) univ) < ⊤ ∧
    (d 0 - ε) / (e 0 + ε) * (ν univ).toReal ≤
      (μ (tubeS H (κ '' ball 0 ρ) univ)).toReal / (volume (ball (0 : EuclideanSpace ℝ ι) ρ)).toReal ∧
    (μ (tubeS H (κ '' ball 0 ρ) univ)).toReal / (volume (ball (0 : EuclideanSpace ℝ ι) ρ)).toReal ≤
      (d 0 + ε) / (e 0 - ε) * (ν univ).toReal := by sorry
