-- Prove2me | Theorems.Thm_ProbabilityTheory_isCadlag_piecewisePath
-- name    : ProbabilityTheory.isCadlag_piecewisePath
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T22:56:50.934434+00:00
-- url     : https://prove2.me/theorems/23c77f44-b40b-408d-92fc-52aa7e2af916
-- title:
--   LeanLevy: ProbabilityTheory.isCadlag_piecewisePath
-- statement:
--   A piecewise-affine jump path is càdlàg: right-continuous everywhere with left limits Exact extracted Lean theorem type; proof pending Prove2Me verification.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Processes/PiecewisePath.lean#L226

import Definitions.Def_LeanLevy_Processes_PiecewisePath
import Definitions.Def_LeanLevy_Processes_Cadlag
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Order.Lattice.Nat
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Mul

theorem ProbabilityTheory.isCadlag_piecewisePath : ∀ {x₀ b : Real} {T Y : Nat → Real},
  @StrictMono Nat Real Nat.instPreorder Real.instPreorder T →
    @Filter.Tendsto Nat Real T (@Filter.atTop Nat Nat.instPreorder) (@Filter.atTop Real Real.instPreorder) →
      @ProbabilityTheory.IsCadlag Real Real
        (@UniformSpace.toTopologicalSpace Real (@PseudoMetricSpace.toUniformSpace Real Real.pseudoMetricSpace))
        (@UniformSpace.toTopologicalSpace Real (@PseudoMetricSpace.toUniformSpace Real Real.pseudoMetricSpace))
        Real.instPreorder (ProbabilityTheory.piecewisePath x₀ b T Y) := by sorry
