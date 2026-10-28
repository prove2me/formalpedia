-- Prove2me | Theorems.Thm_Sensitivity213981Formal_ThreeBoundEndpoint22Packed_packedCodeCheck_eq
-- name    : Sensitivity213981Formal.ThreeBoundEndpoint22Packed.packedCodeCheck_eq
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-26T20:58:14.603294+00:00
-- url     : https://prove2.me/theorems/1c140117-3cf7-41d1-954a-8b1fe7cc5f98
-- title:
--   packed Code Check eq — Boolean sensitivity certificate
-- statement:
--   The following universally quantified assertion holds for the finite sets, Boolean families, tournament data, and profile coordinates defined in the imported interfaces. Each binder specifies the domain of its variable, and bracketed conditions specify finite or ordered structures.
--
--   $$
--   \forall q:\{0,\ldots,4-1\},\quad \forall \mathit{key}:\mathbb N,\quad \forall \mathit{values}:\operatorname{RankCached.CostValues},\quad \forall \mathit{bound}:\mathbb N,\quad \forall \mathit{code}:\mathbb N,\quad \bigl(\bigl(\operatorname{Endpoint22Records.codeRecord}\bigl(\mathit{code}, 11\bigr) = \operatorname{Endpoint22Records.staticRow}\bigl(\mathit{key}, 11\bigr)\bigr)\Longrightarrow \bigl(\operatorname{Endpoint22Packed.packedCodeCheck}\bigl(q, \operatorname{NatTable.get}\bigl(\operatorname{Endpoint22Records.convertedCodes}, \mathit{key}\bigr), \mathit{values}, \mathit{bound}, \mathit{code}\bigr) = \operatorname{RankAnnotated.fusedCodePreparedCheck}\bigl(q, \operatorname{RankAnnotated.prepared}\bigl(\operatorname{NatTable.get}\bigl(\operatorname{Endpoint22Records.keyCodes}\bigr), \operatorname{Endpoint22Records.convertedValues}, q, \mathit{key}\bigr), \mathit{values}, \mathit{bound}, \mathit{code}\bigr)\bigr)\bigr)
--   $$
--
--   Here $\mathbb B=\{\mathsf{false},\mathsf{true}\}$; $\mathcal P_{\mathrm{fin}}(X)$ denotes the finite subsets of $X$. Named functions and predicates refer to their definitions in the cited source. This result supplies the corresponding packed Code Check eq step in the verified $22$-level sensitivity construction.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22PackedPrepared.lean, lines 84–101.

import Definitions.Def_Sensitivity213981Formal_Endpoint22PackedPrepared
import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_Sensitivity213981Formal_RankConvertedPreparation
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

theorem Sensitivity213981Formal.ThreeBoundEndpoint22Packed.packedCodeCheck_eq :
∀ (q : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) (key : Nat)
  (values : Sensitivity213981Formal.ThreeBoundRankCached.CostValues) (bound code : Nat)
  (he :
    @Eq.{1} Nat
      (Sensitivity213981Formal.ThreeBoundEndpoint22Records.codeRecord code
        (@OfNat.ofNat.{0} Nat (nat_lit 11) (instOfNatNat (nat_lit 11))))
      (Sensitivity213981Formal.ThreeBoundEndpoint22Records.staticRow key
        (@OfNat.ofNat.{0} Nat (nat_lit 11) (instOfNatNat (nat_lit 11))))),
  @Eq.{1} Bool
    (Sensitivity213981Formal.ThreeBoundEndpoint22Packed.packedCodeCheck
      (@Fin.val (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) q)
      (Sensitivity213981Formal.ThreeBoundNumeric.NatTable.get
        Sensitivity213981Formal.ThreeBoundEndpoint22Records.convertedCodes key)
      values bound code)
    (Sensitivity213981Formal.ThreeBoundRankAnnotated.fusedCodePreparedCheck
      (@Fin.val (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) q)
      (Sensitivity213981Formal.ThreeBoundRankAnnotated.prepared
        (Sensitivity213981Formal.ThreeBoundNumeric.NatTable.get
          Sensitivity213981Formal.ThreeBoundEndpoint22Records.keyCodes)
        Sensitivity213981Formal.ThreeBoundEndpoint22Records.convertedValues
        (@Fin.val (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) q) key)
      values bound code) := by sorry
