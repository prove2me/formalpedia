-- Prove2me | Theorems.Thm_Sensitivity213981Formal_ThreeBoundConditional_strictP_refined
-- name    : Sensitivity213981Formal.ThreeBoundConditional.strictP_refined
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-26T19:59:10.592497+00:00
-- url     : https://prove2.me/theorems/9935bc05-2286-4d36-9b1f-3ca557865220
-- title:
--   Target and guard defects sharpen the strict zero-tolerance P bound
-- statement:
--   In a tournament stage with nested child family F, assume t_j≤t_k≤t_l, g_l≤g_k≤g_j, g_j≤t_l, g_l≤t_j and g_l≤t_l. The zero-tolerance parent (t_j,g_j) accepts x and (t_k,g_k) rejects x. Suppose a one-marker coherent dominator set has size at most C, and child bounds A(g_j,t_l)≤a, M(g_l,t_j,t_k)≤m_t, B(g_l,t_k)≤b_k, B(g_l,t_l)≤b_l, D(g_l,t_j,t_k,t_l)≤u and M(g_l,g_k,g_j)≤m_g hold. The upward sensitivity of the parent (t_l,g_l) is bounded by the maximum of Ca+max(2m_t,m_t+b_k,u+b_l), available only if t_j<t_k, and Ca+max(2b_k,2b_l+m_g), available only if g_k<g_j. An unavailable branch has value zero.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; StrictPositive.lean, lines 373–422.

import Definitions.Def_Sensitivity213981Formal_ConditionalOrdinary
import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_Sensitivity213981Formal_StrictPositive
import Definitions.Def_Sensitivity213981Formal_WitnessLifting
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Sort
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem Sensitivity213981Formal.ThreeBoundConditional.strictP_refined :
∀ {L I V : Type} [inst : LinearOrder.{0} L] [inst_1 : Fintype.{0} I] [inst_2 : Fintype.{0} V]
  (S : Sensitivity213981Formal.ThreeBoundWitness.Stage L I V)
  (hT :
    @Sensitivity213981Formal.TournamentHighRows.IsTournament V
      (@Sensitivity213981Formal.ThreeBoundWitness.Stage.Adj L I V S))
  (F : L → (I → Bool) → Bool)
  (hF :
    @Sensitivity213981Formal.ThreeBoundProfiles.Nested L I
      (@PartialOrder.toPreorder.{0} L
        (@SemilatticeInf.toPartialOrder.{0} L
          (@Lattice.toSemilatticeInf.{0} L
            (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst)))))
      F)
  (tj tk tl gj gk gl : L)
  (htjk :
    @LE.le.{0} L
      (@Preorder.toLE.{0} L
        (@PartialOrder.toPreorder.{0} L
          (@SemilatticeInf.toPartialOrder.{0} L
            (@Lattice.toSemilatticeInf.{0} L
              (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst))))))
      tj tk)
  (htkl :
    @LE.le.{0} L
      (@Preorder.toLE.{0} L
        (@PartialOrder.toPreorder.{0} L
          (@SemilatticeInf.toPartialOrder.{0} L
            (@Lattice.toSemilatticeInf.{0} L
              (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst))))))
      tk tl)
  (hgkgj :
    @LE.le.{0} L
      (@Preorder.toLE.{0} L
        (@PartialOrder.toPreorder.{0} L
          (@SemilatticeInf.toPartialOrder.{0} L
            (@Lattice.toSemilatticeInf.{0} L
              (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst))))))
      gk gj)
  (hglgk :
    @LE.le.{0} L
      (@Preorder.toLE.{0} L
        (@PartialOrder.toPreorder.{0} L
          (@SemilatticeInf.toPartialOrder.{0} L
            (@Lattice.toSemilatticeInf.{0} L
              (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst))))))
      gl gk)
  (hgjtl :
    @LE.le.{0} L
      (@Preorder.toLE.{0} L
        (@PartialOrder.toPreorder.{0} L
          (@SemilatticeInf.toPartialOrder.{0} L
            (@Lattice.toSemilatticeInf.{0} L
              (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst))))))
      gj tl)
  (hgltj :
    @LE.le.{0} L
      (@Preorder.toLE.{0} L
        (@PartialOrder.toPreorder.{0} L
          (@SemilatticeInf.toPartialOrder.{0} L
            (@Lattice.toSemilatticeInf.{0} L
              (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst))))))
      gl tj)
  (hgltl :
    @LE.le.{0} L
      (@Preorder.toLE.{0} L
        (@PartialOrder.toPreorder.{0} L
          (@SemilatticeInf.toPartialOrder.{0} L
            (@Lattice.toSemilatticeInf.{0} L
              (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst))))))
      gl tl)
  (cap a mₜ bₖ bₗ u m₉ : Nat)
  (hcap :
    @Sensitivity213981Formal.ResidualCaps.DominatorCardBound V
      (fun (a b : V) => Classical.propDecidable (@Eq.{1} V a b))
      (@Sensitivity213981Formal.ThreeBoundWitness.Stage.Adj L I V S)
      (@Sensitivity213981Formal.ThreeBoundWitness.Stage.label L I V S)
      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) cap
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (ha : @Sensitivity213981Formal.ThreeBoundProfiles.ABound L I inst_1 F gj tl a)
  (hmₜ : @Sensitivity213981Formal.ThreeBoundProfiles.MBound L I inst_1 F gl tj tk mₜ)
  (hbₖ : @Sensitivity213981Formal.ThreeBoundProfiles.BBound L I inst_1 F gl tk bₖ)
  (hbₗ : @Sensitivity213981Formal.ThreeBoundProfiles.BBound L I inst_1 F gl tl bₗ)
  (hu : @Sensitivity213981Formal.ThreeBoundProfiles.DBound L I inst_1 F gl tj tk tl u)
  (hm₉ : @Sensitivity213981Formal.ThreeBoundProfiles.MBound L I inst_1 F gl gk gj m₉)
  (x : Prod.{0, 0} (Prod.{0, 0} V Bool) I → Bool)
  (hxj :
    @Eq.{1} Bool
      (@Sensitivity213981Formal.ThreeBoundConditional.ordinaryParent L I V inst_2 S F tj gj
        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) x)
      Bool.true)
  (hxk :
    @Eq.{1} Bool
      (@Sensitivity213981Formal.ThreeBoundConditional.ordinaryParent L I V inst_2 S F tk gk
        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) x)
      Bool.false),
  @LE.le.{0} Nat instLENat
    (@Finset.card.{0} (Prod.{0, 0} (Prod.{0, 0} V Bool) I)
      (@Sensitivity213981Formal.ThreeBoundProfiles.flipsTo (Prod.{0, 0} (Prod.{0, 0} V Bool) I)
        (@instFintypeProd.{0, 0} (Prod.{0, 0} V Bool) I (@instFintypeProd.{0, 0} V Bool inst_2 Bool.fintype) inst_1)
        (@Sensitivity213981Formal.ThreeBoundConditional.ordinaryParent L I V inst_2 S F tl gl
          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        Bool.true x))
    (@Max.max.{0} Nat Nat.instMax
      (@ite.{1} Nat
        (@LT.lt.{0} L
          (@Preorder.toLT.{0} L
            (@PartialOrder.toPreorder.{0} L
              (@SemilatticeInf.toPartialOrder.{0} L
                (@Lattice.toSemilatticeInf.{0} L
                  (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst))))))
          tj tk)
        (@LinearOrder.toDecidableLT.{0} L inst tj tk)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) cap a)
          (@Max.max.{0} Nat Nat.instMax
            (@Max.max.{0} Nat Nat.instMax
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) mₜ)
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) mₜ bₖ))
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) u bₗ)))
        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@ite.{1} Nat
        (@LT.lt.{0} L
          (@Preorder.toLT.{0} L
            (@PartialOrder.toPreorder.{0} L
              (@SemilatticeInf.toPartialOrder.{0} L
                (@Lattice.toSemilatticeInf.{0} L
                  (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst))))))
          gk gj)
        (@LinearOrder.toDecidableLT.{0} L inst gk gj)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) cap a)
          (@Max.max.{0} Nat Nat.instMax
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) bₖ)
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) bₗ)
              m₉)))
        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))) := by sorry
