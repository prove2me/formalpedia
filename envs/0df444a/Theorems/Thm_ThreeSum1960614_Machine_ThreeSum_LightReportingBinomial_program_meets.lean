-- Prove2me | Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightReportingBinomial_program_meets
-- name    : ThreeSum1960614.Machine.ThreeSum.LightReportingBinomial.program_meets
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-15T06:47:35.53314+00:00
-- url     : https://prove2.me/theorems/9ec46fa1-a7d9-42db-88c1-db4ac93cf329
-- title:
--   The binomial lookup program returns the exact coefficient
-- statement:
--   For $k\le n$, initial integer memory $\mu$, scratch base $w$, and depth $d$, suppose addresses fit words, the Pascal table fits memory, $2^{n+1}$ fits a word, and $d+3$ is allowed. Procedure 4 of the fixed program returns $\binom nk$ within its stated time and changes only the Pascal scratch region.
--
--   This lookup computes the exact binomial counts used to size reporting layers and terminal candidate arrays.
-- source:
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightReportingBinomial.lean#L23-L46

import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Syntax
import Definitions.Def_APSPSource_ThreeSumApsp_Util_Index
import Definitions.Def_APSPSource_ThreeSumApsp_Util_List
import Definitions.Def_ThreeSum1960614_Machine_Bundle003
import Definitions.Def_ThreeSum1960614_Machine_Bundle004
import Definitions.Def_ThreeSum1960614_Machine_Bundle005
import Definitions.Def_ThreeSum1960614_Machine_Bundle006
import Definitions.Def_ThreeSum1960614_Machine_Bundle007
import Definitions.Def_ThreeSum1960614_Machine_Bundle008
import Definitions.Def_ThreeSum1960614_Machine_Bundle010
import Definitions.Def_ThreeSum1960614_Machine_Bundle012
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle02
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle06
import Lean
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Data.Int.Notation
import Mathlib.Data.List.GetD
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.SuccPred
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Logic.Function.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightPascal_build_meets

namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.LightPascal
end ThreeSum.LightPascal
namespace ThreeSum.LightReportingBinomial
end ThreeSum.LightReportingBinomial
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.LightPascal
end ThreeSum1960614.Machine.ThreeSum.LightPascal
namespace ThreeSum1960614.Machine.ThreeSum.LightReportingBinomial
end ThreeSum1960614.Machine.ThreeSum.LightReportingBinomial

open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.LightReportingBinomial
open _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingBinomial

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.LightPascal
open _root_.ThreeSum1960614.Machine.ThreeSum.LightPascal
set_option maxHeartbeats 1000000
set_option maxRecDepth 8000
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits}

theorem ThreeSum1960614.Machine.ThreeSum.LightReportingBinomial.program_meets {μ : ℕ→ℤ} {n k work d : ℕ}
    (hk : k≤n) (hw : (lim.space : ℤ)≤lim.word)
    (hspace : work+_root_.ThreeSum.LightPascal.tableSize n≤lim.space)
    (hword : ((2^(n+1) : ℕ) : ℤ)≤lim.word) (hd : d+3≤lim.depth) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingBinomial.program 4 d [n,k,work] μ (_root_.ThreeSum.LightReportingBinomial.time n)
      (fun r ν => r=(n.choose k : ℤ) ∧ _root_.ThreeSum1960614.Machine.Light.SameOutside μ ν work (_root_.ThreeSum.LightPascal.tableSize n)) := by sorry
