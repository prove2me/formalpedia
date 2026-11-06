-- Prove2me | Theorems.Thm_ProbabilityTheory_increment_apply
-- name    : ProbabilityTheory.increment_apply
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T22:13:25.632037+00:00
-- url     : https://prove2.me/theorems/28fde53d-5585-421c-96f0-ccaf37dba6a4
-- title:
--   LeanLevy: ProbabilityTheory.increment_apply
-- statement:
--   The increment of a process `X` from time `s` to time `t`. Exact extracted Lean theorem type; proof pending Prove2Me verification.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4//home/willr/projects/Prove2Me/scratch/leanlevy_bulk_20261027/source/LeanLevy/Processes/StochasticProcess.lean#L48

import Definitions.Def_LeanLevy_Processes_StochasticProcess
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.IdentDistrib
import Mathlib.MeasureTheory.Group.Arithmetic
import Mathlib.Probability.Process.Adapted
import Mathlib.Probability.Process.Filtration
import Mathlib.Probability.Independence.Process.HasIndepIncrements.Basic

universe u_1 u_2 u_3
theorem ProbabilityTheory.increment_apply : ∀ {ι : Type u_1} {Ω : Type u_2} {E : Type u_3} [inst : Sub E] (X : ι → Ω → E) (s t : ι) (ω : Ω),
  @Eq E (@ProbabilityTheory.increment ι Ω E inst X s t ω) (@HSub.hSub E E E (@instHSub E inst) (X t ω) (X s ω)) := by sorry
