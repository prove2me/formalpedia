-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_LUPf_diffOn_inv
-- name    : ReciprocityTheory.ChartRestriction.G.AR.Up.LUPf.diffOn_inv
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T13:20:58.16+00:00
-- url     : https://prove2.me/theorems/1f381149-cefe-492e-9d53-2214c116166b
-- title:
--   LUPf: diff On inv
-- statement:
--   The LUPf construction uses the diff On inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/LUStatementPfC.lean#L24-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/LUStatementPfC.lean#L24-L38

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_LUStatementPfB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_LUStatementPfC
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.LUPf
open Matrix NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates ReciprocityTheory.ChartRestriction.G.AR.Up.ExtFPf
  Metric
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : Data E r} {x0 : Frame X.Ψ r}

theorem ReciprocityTheory.ChartRestriction.G.AR.Up.LUPf.diffOn_inv {k : ℕ} {s : Set (Frame X.Ψ r)} (m : Frame X.Ψ r → Matrix (Fin k) (Fin k) ℂ)
    (hm : ∀ i j, DifferentiableOn ℂ (fun x => m x i j) s) (hd : ∀ x ∈ s, (m x).det ≠ 0) :
    ∀ i j, DifferentiableOn ℂ (fun x => (m x)⁻¹ i j) s := by sorry
