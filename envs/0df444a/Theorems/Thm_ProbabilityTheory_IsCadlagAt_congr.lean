-- Prove2me | Theorems.Thm_ProbabilityTheory_IsCadlagAt_congr
-- name    : ProbabilityTheory.IsCadlagAt.congr
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T22:22:26.232671+00:00
-- url     : https://prove2.me/theorems/9c12727f-62a0-4f32-ac0c-24eb9e6f8d1f
-- title:
--   LeanLevy: ProbabilityTheory.IsCadlagAt.congr
-- statement:
--   Being càdlàg at a point depends only on the germ of the function at `𝓝 t`: if `f` and `g` Exact extracted Lean theorem type; proof pending Prove2Me verification.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Processes/Cadlag.lean#L136

import Definitions.Def_LeanLevy_Processes_Cadlag
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.Order.Preorder.Finite
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Topology.Algebra.Monoid

universe u_1 u_2
theorem ProbabilityTheory.IsCadlagAt.congr : ∀ {α : Type u_1} {β : Type u_2} [inst : TopologicalSpace α] [inst_1 : TopologicalSpace β] [inst_2 : Preorder α]
  {f g : α → β} {t : α},
  @ProbabilityTheory.IsCadlagAt α β inst inst_1 inst_2 f t →
    @Filter.EventuallyEq α β (@nhds α inst t) f g → @ProbabilityTheory.IsCadlagAt α β inst inst_1 inst_2 g t := by sorry
