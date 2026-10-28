-- Prove2me | Theorems.Thm_Sensitivity213981Formal_ThreeBoundEndpoint22TypeSplit_filteredPrefix_eq_nil_of_budget
-- name    : Sensitivity213981Formal.ThreeBoundEndpoint22TypeSplit.filteredPrefix_eq_nil_of_budget
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-27T01:57:15.926913+00:00
-- url     : https://prove2.me/theorems/255a766c-c548-40f7-98bd-4fa3a84ce3a7
-- title:
--   filtered Prefix eq nil of budget — Boolean sensitivity certificate
-- statement:
--   The following universally quantified assertion holds for the finite sets, Boolean families, tournament data, and profile coordinates defined in the imported interfaces. Each binder specifies the domain of its variable, and bracketed conditions specify finite or ordered structures.
--
--   $$
--   \forall \mathit{pref}:\operatorname{List}(\operatorname{Q3.Kind}),\quad \forall \mathit{lo}:\mathbb N,\quad \forall n:\mathbb N,\quad \bigl(\neg \bigl(\frac{\bigl(\bigl(|\mathit{pref}|+n\bigr)\cdot \bigl(\bigl(|\mathit{pref}|+n\bigr)-1\bigr)\bigr)}{2} \le \bigl(\operatorname{List.sum}\bigl(\operatorname{List.map}\bigl(\operatorname{Q3.budget}, \mathit{pref}\bigr)\bigr)+\bigl(4\cdot n\bigr)\bigr)\bigr)\Longrightarrow \bigl(\operatorname{Endpoint22TypeSplit.filteredPrefix}\bigl(\mathit{pref}, \mathit{lo}, n\bigr) = \langle\rangle\bigr)\bigr)
--   $$
--
--   Here $\mathbb B=\{\mathsf{false},\mathsf{true}\}$; $\mathcal P_{\mathrm{fin}}(X)$ denotes the finite subsets of $X$. Named functions and predicates refer to their definitions in the cited source. This result supplies the corresponding filtered Prefix eq nil of budget step in the verified $22$-level sensitivity construction.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22TypePruning.lean, lines 42–64.

import Definitions.Def_Sensitivity213981Formal_Endpoint22TypeSplit
import Definitions.Def_Sensitivity213981Formal_HighTypeCore
import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Sort
import Mathlib.Data.List.TakeDrop
import Mathlib.Data.Prod.Lex
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem Sensitivity213981Formal.ThreeBoundEndpoint22TypeSplit.filteredPrefix_eq_nil_of_budget :
∀ (pref : List.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind) (lo n : Nat)
  (hbad :
    Not
      (@LE.le.{0} Nat instLENat
        (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv)
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind pref) n)
            (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind pref) n)
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@List.sum.{0} Nat instAddNat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass)
            (@List.map.{0, 0}
              (Sensitivity213981Formal.ThreeBoundHighTypes.Kind
                (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
              Nat Sensitivity213981Formal.ThreeBoundQ3.budget pref))
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) n)))),
  @Eq.{1} (List.{0} (List.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind))
    (Sensitivity213981Formal.ThreeBoundEndpoint22TypeSplit.filteredPrefix pref lo n)
    (@List.nil.{0} (List.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind)) := by sorry
