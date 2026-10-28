-- Prove2me | Theorems.Thm_Sensitivity213981Formal_ThreeBoundRankNumeric_kind_target_prefix_iff
-- name    : Sensitivity213981Formal.ThreeBoundRankNumeric.kind_target_prefix_iff
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-26T20:17:57.720702+00:00
-- url     : https://prove2.me/theorems/96365369-86b3-4ded-bff2-099cab24b199
-- title:
--   kind target prefix iff — Boolean sensitivity certificate
-- statement:
--   The following universally quantified assertion holds for the finite sets, Boolean families, tournament data, and profile coordinates defined in the imported interfaces. Each binder specifies the domain of its variable, and bracketed conditions specify finite or ordered structures.
--
--   $$
--   \forall L:\mathcal U,\quad \forall I:\mathcal U,\quad \forall V:\mathcal U,\quad \bigl[\operatorname{LinearOrder}\bigl(L\bigr)\bigr]\;\bigl[\mathrm{finite}(I)\bigr]\;\bigl[\mathrm{finite}(V)\bigr]\;\forall S:\operatorname{Witness.Stage}\bigl(L, I, V\bigr),\quad \forall F:\left(L\to \left(\left(I\to \mathbb B\right)\to \mathbb B\right)\right),\quad \bigl(\operatorname{Profiles.Nested}\bigl(F\bigr)\Longrightarrow \forall i:L,\quad \forall j:L,\quad \forall P:\operatorname{MinmaxTransfer.PairData}\bigl(S, F, i, j\bigr),\quad \forall x:\left(V\times \mathbb B\times I\to \mathbb B\right),\quad \bigl(\bigl(\operatorname{Stage.tolerance}\bigl(S, j\bigr) \le 3\bigr)\Longrightarrow \forall w:V,\quad \forall \mathit{kind}:\{0,\ldots,11-1\},\quad \bigl(\operatorname{HighTypes.OfKind}\bigl(3, \operatorname{MinmaxCandidates.PositiveCandidate}\bigl(S, F, \operatorname{PairData.strongLower}\bigl(P\bigr), \operatorname{PairData.strongUpper}\bigl(P\bigr), j, x, w\bigr), \operatorname{MinmaxCandidates.GuardCandidate}\bigl(S, F, \operatorname{PairData.strongLower}\bigl(P\bigr), \operatorname{PairData.strongUpper}\bigl(P\bigr), j, x, w\bigr), \mathit{kind}\bigr)\Longrightarrow \forall q:\mathbb N,\quad \bigl(w\in \operatorname{MinmaxCandidates.targetPrefix}\bigl(S, F, \operatorname{PairData.strongLower}\bigl(P\bigr), \operatorname{PairData.strongUpper}\bigl(P\bigr), j, x, q\bigr) \Longleftrightarrow \bigl(\operatorname{HighTypes.positivePrefix}\bigl(3, q, \mathit{kind}\bigr) = \mathsf{true}\bigr)\bigr)\bigr)\bigr)\bigr)
--   $$
--
--   Here $\mathbb B=\{\mathsf{false},\mathsf{true}\}$; $\mathcal P_{\mathrm{fin}}(X)$ denotes the finite subsets of $X$. Named functions and predicates refer to their definitions in the cited source. This result supplies the corresponding kind target prefix iff step in the verified $22$-level sensitivity construction.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; RankTypeStats.lean, lines 18–38.

import Definitions.Def_Sensitivity213981Formal_HighTypeCore
import Definitions.Def_Sensitivity213981Formal_MinmaxCandidates
import Definitions.Def_Sensitivity213981Formal_MinmaxPairData
import Definitions.Def_Sensitivity213981Formal_MinmaxPrefixCaps
import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_Sensitivity213981Formal_RankCapData
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.GroupWithZero.Units.Equiv
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.Digraph.Basic
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Sort
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.NumberTheory.JacobiSum.Basic
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem Sensitivity213981Formal.ThreeBoundRankNumeric.kind_target_prefix_iff :
∀ {L I V : Type} [inst : LinearOrder.{0} L] [Fintype.{0} I] [inst_2 : Fintype.{0} V]
  (S : Sensitivity213981Formal.ThreeBoundWitness.Stage L I V) (F : L → (I → Bool) → Bool)
  (hF :
    @Sensitivity213981Formal.ThreeBoundProfiles.Nested L I
      (@PartialOrder.toPreorder.{0} L
        (@SemilatticeInf.toPartialOrder.{0} L
          (@Lattice.toSemilatticeInf.{0} L
            (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst)))))
      F)
  (i j : L)
  (P :
    @Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData L I V
      (@PartialOrder.toPreorder.{0} L
        (@SemilatticeInf.toPartialOrder.{0} L
          (@Lattice.toSemilatticeInf.{0} L
            (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst)))))
      S F i j)
  (x : Prod.{0, 0} (Prod.{0, 0} V Bool) I → Bool)
  (hQ :
    @LE.le.{0} Nat instLENat (@Sensitivity213981Formal.ThreeBoundWitness.Stage.tolerance L I V S j)
      (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
  (w : V) (kind : Fin (@OfNat.ofNat.{0} Nat (nat_lit 11) (instOfNatNat (nat_lit 11))))
  (hk :
    Sensitivity213981Formal.ThreeBoundHighTypes.OfKind (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
      (@Sensitivity213981Formal.ThreeBoundMinmaxCandidates.PositiveCandidate L I V inst_2 S F
        (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongLower L I V
          (@PartialOrder.toPreorder.{0} L
            (@SemilatticeInf.toPartialOrder.{0} L
              (@Lattice.toSemilatticeInf.{0} L
                (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst)))))
          S F i j P)
        (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongUpper L I V
          (@PartialOrder.toPreorder.{0} L
            (@SemilatticeInf.toPartialOrder.{0} L
              (@Lattice.toSemilatticeInf.{0} L
                (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst)))))
          S F i j P)
        j x w)
      (@Sensitivity213981Formal.ThreeBoundMinmaxCandidates.GuardCandidate L I V inst_2 S F
        (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongLower L I V
          (@PartialOrder.toPreorder.{0} L
            (@SemilatticeInf.toPartialOrder.{0} L
              (@Lattice.toSemilatticeInf.{0} L
                (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst)))))
          S F i j P)
        (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongUpper L I V
          (@PartialOrder.toPreorder.{0} L
            (@SemilatticeInf.toPartialOrder.{0} L
              (@Lattice.toSemilatticeInf.{0} L
                (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst)))))
          S F i j P)
        j x w)
      kind)
  (q : Nat),
  Iff
    (@Membership.mem.{0, 0} V (Finset.{0} V)
      (@SetLike.instMembership.{0, 0} (Finset.{0} V) V (@Finset.instSetLike.{0} V))
      (@Sensitivity213981Formal.ThreeBoundMinmaxCandidates.targetPrefix L I V inst_2 S F
        (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongLower L I V
          (@PartialOrder.toPreorder.{0} L
            (@SemilatticeInf.toPartialOrder.{0} L
              (@Lattice.toSemilatticeInf.{0} L
                (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst)))))
          S F i j P)
        (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongUpper L I V
          (@PartialOrder.toPreorder.{0} L
            (@SemilatticeInf.toPartialOrder.{0} L
              (@Lattice.toSemilatticeInf.{0} L
                (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst)))))
          S F i j P)
        j x q)
      w)
    (@Eq.{1} Bool
      (Sensitivity213981Formal.ThreeBoundHighTypes.positivePrefix
        (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) q kind)
      Bool.true) := by sorry
