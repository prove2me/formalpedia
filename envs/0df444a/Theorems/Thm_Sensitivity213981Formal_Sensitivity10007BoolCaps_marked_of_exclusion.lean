-- Prove2me | Theorems.Thm_Sensitivity213981Formal_Sensitivity10007BoolCaps_marked_of_exclusion
-- name    : Sensitivity213981Formal.Sensitivity10007BoolCaps.marked_of_exclusion
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-26T20:01:22.09811+00:00
-- url     : https://prove2.me/theorems/b8b3550b-0953-47a5-98bb-2ea70940d5f3
-- title:
--   marked of exclusion — Boolean sensitivity certificate
-- statement:
--   The following universally quantified assertion holds for the finite sets, Boolean families, tournament data, and profile coordinates defined in the imported interfaces. Each binder specifies the domain of its variable, and bracketed conditions specify finite or ordered structures.
--
--   $$
--   \forall V:\mathcal U,\quad \bigl[\mathrm{finite}(V)\bigr]\;\forall R:\left(V\to \left(V\to \mathrm{Prop}\right)\right),\quad \forall \mathit{ell}:\left(V\times V\to \{0,\ldots,2-1\}\right),\quad \forall q:\mathbb N,\quad \forall a:\mathbb N,\quad \forall m:\mathbb N,\quad \forall B:\mathbb N,\quad \bigl(\forall J:\operatorname{ZL.MarkedIndex}\bigl(V, a, m\bigr),\quad \neg \operatorname{SupportedFamily.bad}\bigl(\operatorname{ZL.markedFamily}\bigl(R, q, a, m, B\bigr), J, \mathit{ell}\bigr)\Longrightarrow \operatorname{ResidualCaps.MarkedCardBound}\bigl(R, \operatorname{Sensitivity10007BoolCaps.boolLabel}\bigl(\mathit{ell}\bigr), q, m, B, a\bigr)\bigr)
--   $$
--
--   Here $\mathbb B=\{\mathsf{false},\mathsf{true}\}$; $\mathcal P_{\mathrm{fin}}(X)$ denotes the finite subsets of $X$. Named functions and predicates refer to their definitions in the cited source. This result supplies the corresponding marked of exclusion step in the verified $22$-level sensitivity construction.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; SelectedBoolCaps.lean, lines 141–155.

import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_Sensitivity213981Formal_SelectedBoolCaps
import Definitions.Def_Sensitivity213981Formal_Supplement_CandidateCoherence
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.GroupWithZero.Units.Equiv
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
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
import Mathlib.Data.List.Sort
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Choose.Basic
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

theorem Sensitivity213981Formal.Sensitivity10007BoolCaps.marked_of_exclusion :
∀ {V : Type} [inst : Fintype.{0} V] [inst_1 : DecidableEq.{1} V] (R : V → V → Prop)
  (ell : Prod.{0, 0} V V → Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) (q a m B : Nat)
  (hex :
    ∀ (J : @Sensitivity213981Formal.Sensitivity10007Labeling.ZL.MarkedIndex.{0} V inst inst_1 a m),
      Not
        (@Sensitivity213981Formal.Sensitivity10007Labeling.ZL.SupportedFamily.bad.{0, 0} (Prod.{0, 0} V V)
          (@Sensitivity213981Formal.Sensitivity10007Labeling.ZL.MarkedIndex.{0} V inst inst_1 a m)
          (fun (a b : Prod.{0, 0} V V) => @instDecidableEqProd.{0, 0} V V inst_1 inst_1 a b)
          (@Sensitivity213981Formal.Sensitivity10007Labeling.ZL.markedFamily.{0} V inst inst_1 R q a m B) J ell)),
  @Sensitivity213981Formal.ResidualCaps.MarkedCardBound V R
    (@Sensitivity213981Formal.Sensitivity10007BoolCaps.boolLabel V ell) q m B a := by sorry
