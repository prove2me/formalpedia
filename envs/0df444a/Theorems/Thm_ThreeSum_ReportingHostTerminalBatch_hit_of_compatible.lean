-- Prove2me | Theorems.Thm_ThreeSum_ReportingHostTerminalBatch_hit_of_compatible
-- name    : ThreeSum.ReportingHostTerminalBatch.hit_of_compatible
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-14T15:02:47.004734+00:00
-- url     : https://prove2.me/theorems/03d509e8-4fd1-4793-a2c1-ad12e27800a8
-- title:
--   A compatible original pair produces a terminal-batch hit
-- statement:
--   Let $B,C$ be finite sets in finite types with decidable equality, with integer values $b,c$. Suppose bijections $e_L:[N_L]\simeq B$ and $e_R:[N_R]\simeq C$ enumerate arrays satisfying $\mathrm{left}_i=b(e_L(i))$ and $\mathrm{right}_j=c(e_R(j))$. Fix natural $p,h,J,k$, integer shift $s$, and target $a$, with $k\le J$.
--
--   Let $q$ be a global output, and let $u$ be a valid length-$k$ prefix choosing an $h$-element subset of each corresponding output block. Suppose a choice tuple $t$ has output $q$ and prefix $u$. If $(\beta,\gamma)\in B\times C$ satisfies, for the global modulus $M$,
--   $$
--   M\mid b(\beta)\bmod p-\operatorname{tupleLeft}(t),\quad
--   M\mid c(\gamma)\bmod p+s-\operatorname{tupleRight}(t),\quad
--   c(\gamma)-b(\beta)-a=0,
--   $$
--   then $\operatorname{Hit}(a,p,s,\mathrm{left},\mathrm{right},N_L,N_R,q,k,u)$ holds: some enumerated terminal candidate has both flags enabled and matching source buckets containing a pair solving the original equation.
--
--   This supplies completeness of the terminal batch for compatible original pairs.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/ReportingHostTerminalBatch.lean#L112-L141

import Aesop
import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Logic
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle03
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle07
import Definitions.Def_ThreeSum1962Source_Bundle08
import Definitions.Def_ThreeSum1962Source_Bundle09
import Definitions.Def_ThreeSum1962Source_Bundle10
import Definitions.Def_ThreeSum1962Source_Bundle11
import Definitions.Def_ThreeSum1962Source_Bundle12
import Definitions.Def_ThreeSum1962Source_Bundle13
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Algebra.Ring.Nat
import Mathlib.Combinatorics.Colex
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Range
import Mathlib.Data.Finset.Sigma
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Int.Notation
import Mathlib.Data.Int.SuccPred
import Mathlib.Data.List.Basic
import Mathlib.Data.List.GetD
import Mathlib.Data.List.MinMax
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Pi
import Mathlib.Data.List.ProdSigma
import Mathlib.Data.List.Sublists
import Mathlib.Data.List.TakeDrop
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Nat.SuccPred
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.Index
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Dual
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Function.Basic
import Mathlib.NumberTheory.Bertrand
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.Abel
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto
import Theorems.Thm_ThreeSum_BlockForced_forced_disjoint
import Theorems.Thm_ThreeSum_BlockForced_forced_union
import Theorems.Thm_ThreeSum_ReportingHostTerminalChoices_mem_choices


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light
namespace ThreeSum.BlockEncoding
end ThreeSum.BlockEncoding
namespace ThreeSum.BlockForced
end ThreeSum.BlockForced
namespace ThreeSum.BlockIndex
end ThreeSum.BlockIndex
namespace ThreeSum.BlockIndexedQuery
end ThreeSum.BlockIndexedQuery
namespace ThreeSum.BlockRows
end ThreeSum.BlockRows
namespace ThreeSum.BlockSourceEncoding
end ThreeSum.BlockSourceEncoding
namespace ThreeSum.GlobalEncoding
end ThreeSum.GlobalEncoding
namespace ThreeSum.LightBlockSourceBuild
end ThreeSum.LightBlockSourceBuild
namespace ThreeSum.LightReportingTerminalMasks
end ThreeSum.LightReportingTerminalMasks
namespace ThreeSum.LightSourceResidues
end ThreeSum.LightSourceResidues
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.LocalGraph
end ThreeSum.LocalGraph
namespace ThreeSum.LocalHashMoments
end ThreeSum.LocalHashMoments
namespace ThreeSum.QueryCoordinates
end ThreeSum.QueryCoordinates
namespace ThreeSum.RawIncidences
end ThreeSum.RawIncidences
namespace ThreeSum.RawPrefixCounts
end ThreeSum.RawPrefixCounts
namespace ThreeSum.RawReporting
end ThreeSum.RawReporting
namespace ThreeSum.ReportingHostBlockBucketTest
end ThreeSum.ReportingHostBlockBucketTest
namespace ThreeSum.ReportingHostTerminalChoices
end ThreeSum.ReportingHostTerminalChoices
namespace ThreeSum.StoredReporting
end ThreeSum.StoredReporting
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress

universe u_2 u_3

theorem ThreeSum.ReportingHostTerminalBatch.hit_of_compatible : ∀ {β : Type u_2} {γ : Type u_3} [Fintype.{u_2} β] [Fintype.{u_3} γ] [DecidableEq.{u_2 + 1} β] [DecidableEq.{u_3 + 1} γ]
  {h J k NL NR : Nat} (p : Nat) (shift av : Int) (B : Finset.{u_2} β) (C : Finset.{u_3} γ) (b : β → Int) (c : γ → Int)
  (left right : Nat → Int) (eL : Equiv.{1, u_2 + 1} (Fin NL) ↥B) (eR : Equiv.{1, u_3 + 1} (Fin NR) ↥C)
  (hvL :
    ∀ (i : Fin NL),
      @Eq.{1} Int (left (@Fin.val NL i))
        (b
          (@Subtype.val.{u_2 + 1} β
            (fun (x : β) =>
              @Membership.mem.{u_2, u_2} β (Finset.{u_2} β)
                (@SetLike.instMembership.{u_2, u_2} (Finset.{u_2} β) β (@Finset.instSetLike.{u_2} β)) B x)
            (@DFunLike.coe.{u_2 + 1, 1, u_2 + 1} (Equiv.{1, u_2 + 1} (Fin NL) ↥B) (Fin NL) (fun (x : Fin NL) => ↥B)
              (@EquivLike.toFunLike.{u_2 + 1, 1, u_2 + 1} (Equiv.{1, u_2 + 1} (Fin NL) ↥B) (Fin NL) (↥B)
                (@Equiv.instEquivLike.{1, u_2 + 1} (Fin NL) ↥B))
              eL i))))
  (hvR :
    ∀ (j : Fin NR),
      @Eq.{1} Int (right (@Fin.val NR j))
        (c
          (@Subtype.val.{u_3 + 1} γ
            (fun (x : γ) =>
              @Membership.mem.{u_3, u_3} γ (Finset.{u_3} γ)
                (@SetLike.instMembership.{u_3, u_3} (Finset.{u_3} γ) γ (@Finset.instSetLike.{u_3} γ)) C x)
            (@DFunLike.coe.{u_3 + 1, 1, u_3 + 1} (Equiv.{1, u_3 + 1} (Fin NR) ↥C) (Fin NR) (fun (x : Fin NR) => ↥C)
              (@EquivLike.toFunLike.{u_3 + 1, 1, u_3 + 1} (Equiv.{1, u_3 + 1} (Fin NR) ↥C) (Fin NR) (↥C)
                (@Equiv.instEquivLike.{1, u_3 + 1} (Fin NR) ↥C))
              eR j))))
  (q : ThreeSum.GlobalEncoding.GlobalOutput h J)
  (pre :
    List.{0}
      (Finset.{0}
        (Fin
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h))))
  (hk : @LE.le.{0} Nat instLENat k J) (hp : @ThreeSum.StoredReporting.ValidPrefix h J q k pre)
  (t : ThreeSum.RawIncidences.ChoiceTuple h J)
  (ht :
    @Membership.mem.{0, 0} (ThreeSum.RawIncidences.ChoiceTuple h J)
      (Finset.{0} (ThreeSum.RawIncidences.ChoiceTuple h J))
      (@SetLike.instMembership.{0, 0} (Finset.{0} (ThreeSum.RawIncidences.ChoiceTuple h J))
        (ThreeSum.RawIncidences.ChoiceTuple h J) (@Finset.instSetLike.{0} (ThreeSum.RawIncidences.ChoiceTuple h J)))
      (@ThreeSum.RawPrefixCounts.completions h J q k pre) t)
  (bc : Prod.{u_2, u_3} β γ)
  (hbc :
    @Membership.mem.{max u_2 u_3, max u_3 u_2} (Prod.{u_2, u_3} β γ) (Finset.{max u_2 u_3} (Prod.{u_2, u_3} β γ))
      (@SetLike.instMembership.{max u_2 u_3, max u_2 u_3} (Finset.{max u_2 u_3} (Prod.{u_2, u_3} β γ))
        (Prod.{u_2, u_3} β γ) (@Finset.instSetLike.{max u_2 u_3} (Prod.{u_2, u_3} β γ)))
      (@ThreeSum.RawPrefixCounts.compatiblePairs.{u_2, u_3} β γ h J (@Nat.cast.{0} Int instNatCastInt p) shift B C b c
        t)
      bc)
  (heq :
    @Eq.{1} Int
      (@HSub.hSub.{0, 0, 0} Int Int Int (@instHSub.{0} Int Int.instSub)
        (@HSub.hSub.{0, 0, 0} Int Int Int (@instHSub.{0} Int Int.instSub) (c (@Prod.snd.{u_2, u_3} β γ bc))
          (b (@Prod.fst.{u_2, u_3} β γ bc)))
        av)
      (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0)))),
  @ThreeSum.ReportingHostTerminalBatch.Hit h J av p shift left right NL NR q k pre := by
  sorry
