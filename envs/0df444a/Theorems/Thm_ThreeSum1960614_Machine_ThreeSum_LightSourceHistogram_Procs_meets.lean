-- Prove2me | Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightSourceHistogram_Procs_meets
-- name    : ThreeSum1960614.Machine.ThreeSum.LightSourceHistogram.Procs.meets
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-15T06:36:03.334987+00:00
-- url     : https://prove2.me/theorems/0d69e215-ca1e-4e12-a09d-d5e62e06603f
-- title:
--   Execution of a two-modulus original-source histogram
-- statement:
--   Let $p,m>0$, input count $n$, original magnitude bound $U$, shift bound $D$, and shift $\delta\in\mathbb Z$ satisfy $|\delta|\le D$. Suppose memory $\mu$ stores the original source at $s$ with $|\mu(s+i)|\le U$. Source and histogram end before code scratch, which ends before remainder scratch. Assume addresses fit words, the explicit source-residue space and word budgets fit and $d+1$ is strictly below the depth limit. A literal closure record identifies the key, remainder, histogram and fill procedures. The wrapper writes
--
--   $$k_i=((\mu(s+i)\bmod p)+\delta)\bmod m$$
--
--   as its code array, and counts each code exactly in the length-$m$ histogram. It meets its stated time and preserves cells below the code base outside the histogram.
--
--   This connects source histograms directly to original signed values and the common carry offset.
-- source:
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightSourceHistogram.lean#L42-L82

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
import Definitions.Def_ThreeSum1960614_Machine_Bundle009
import Definitions.Def_ThreeSum1960614_Machine_Bundle010
import Definitions.Def_ThreeSum1960614_Machine_Bundle012
import Definitions.Def_ThreeSum1960614_Machine_Bundle014
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle02
import Definitions.Def_ThreeSum1962Source_Bundle03
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle05
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
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Range
import Mathlib.Data.Int.Notation
import Mathlib.Data.List.GetD
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Nat.SuccPred
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Logic.Function.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.NormNum
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
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightHistogram_histogram_meets
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightSourceResidues_ends

namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.LightSourceHistogram
end ThreeSum.LightSourceHistogram
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.LightSourceHistogram
end ThreeSum1960614.Machine.ThreeSum.LightSourceHistogram

open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.LightSourceHistogram
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceHistogram

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
set_option maxHeartbeats 1200000
set_option maxRecDepth 10000
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}

theorem ThreeSum1960614.Machine.ThreeSum.LightSourceHistogram.Procs.meets {pMain : ℕ} (S : _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceHistogram.Procs P pMain)
    {μ : ℕ → ℤ} {src hist n p m codes work U D : ℕ} {shift : ℤ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+1 < lim.depth)
    (hp : 0 < p) (hm : 0 < m)
    (hsrc : src+n ≤ codes) (hhist : hist+m ≤ codes) (hcodes : codes+n ≤ work)
    (hspace : _root_.ThreeSum.LightSourceResidues.space work p U D ≤ lim.space)
    (hshift : |shift| ≤ (D : ℤ))
    (hword : (_root_.ThreeSum.LightSourceResidues.word p m U D : ℤ) ≤ lim.word)
    (hvalues : ∀ i < n, |μ (src+i)| ≤ (U : ℤ)) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P pMain d [src,hist,n,p,m,codes,work,shift] μ (_root_.ThreeSum.LightSourceHistogram.time n p m U D)
      (fun _ ν =>
        (∀ i < n, ν (codes+i) =
          (_root_.ThreeSum.LightSourceResidues.key p m shift (μ (src+i)) : ℤ)) ∧
        (∀ r < m, ν (hist+r) = (_root_.ThreeSum.LightHistogram.count
          (fun i => _root_.ThreeSum.LightSourceResidues.key p m shift (μ (src+i))) r n : ℤ)) ∧
        _root_.ThreeSum1960614.Machine.Light.KeptBut μ ν codes hist m) := by sorry
