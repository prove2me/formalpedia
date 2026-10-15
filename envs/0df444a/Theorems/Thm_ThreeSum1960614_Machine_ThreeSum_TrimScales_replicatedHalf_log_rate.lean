-- Prove2me | Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_TrimScales_replicatedHalf_log_rate
-- name    : ThreeSum1960614.Machine.ThreeSum.TrimScales.replicatedHalf_log_rate
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-15T09:08:50.0012+00:00
-- url     : https://prove2.me/theorems/a03fa5d0-1bf5-4dd5-84a6-22ffedb8de95
-- title:
--   Growth of a replicated local quantity
-- statement:
--   Let $f:\mathbb N\to\mathbb N$ and $a\in\mathbb R$. Suppose $$\lim_{h\to\infty}\frac{\log f(h)}{2h\log2}=a.$$ For its specified replicated-half construction $R_f(n)$ at input size $n$, $$\lim_{n\to\infty}\frac{\log R_f(n)}{\log n}=\varepsilon a,$$ where $\varepsilon$ is the fixed inner-size fraction.
--
--   Transfers a local exponential rate to the global input-size exponent. This is a supporting lemma in the complete deterministic integer 3SUM runtime proof.
-- source:
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/TrimScales.lean#L43-L62

import Aesop
import Definitions.Def_ThreeSum1960614_Analysis
import Definitions.Def_ThreeSum1960614_Machine_Bundle001
import Definitions.Def_ThreeSum1960614_Machine_Bundle003
import Definitions.Def_ThreeSum1960614_Machine_Bundle004
import Definitions.Def_ThreeSum1960614_Machine_Bundle005
import Definitions.Def_ThreeSum1960614_Machine_Bundle006
import Definitions.Def_ThreeSum1960614_Machine_Bundle007
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle07
import Lean
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.List.MinMax
import Mathlib.Data.List.Pi
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.Index
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.Dual
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.NumberTheory.Bertrand
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs

namespace Filter
end Filter
namespace Real
end Real
namespace ThreeSum
end ThreeSum
namespace ThreeSum.Scales
end ThreeSum.Scales
namespace ThreeSum.TrimScales
end ThreeSum.TrimScales
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.Scales
end ThreeSum1960614.Machine.ThreeSum.Scales
namespace ThreeSum1960614.Machine.ThreeSum.TrimScales
end ThreeSum1960614.Machine.ThreeSum.TrimScales

open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum1960614.Machine.ThreeSum.TrimScales

open _root_.Filter
open _root_.Real
open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open scoped _root_.Topology
open _root_.ThreeSum1960614.Machine.ThreeSum.TrimScales

theorem ThreeSum1960614.Machine.ThreeSum.TrimScales.replicatedHalf_log_rate {f : ℕ → ℕ} {a : ℝ}
    (hf : Tendsto (fun h : ℕ => Real.log (f h : ℝ) / ((2 * h : ℝ) * Real.log 2))
      atTop (𝓝 a)) :
    Tendsto (fun n : ℕ => Real.log (_root_.ThreeSum1960614.Machine.ThreeSum.TrimScales.replicatedHalf f n : ℝ) / Real.log n) atTop (𝓝 (_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.epsilon * a)) := by sorry
