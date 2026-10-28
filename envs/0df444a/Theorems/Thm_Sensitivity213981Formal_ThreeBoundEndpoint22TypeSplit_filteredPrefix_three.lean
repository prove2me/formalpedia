-- Prove2me | Theorems.Thm_Sensitivity213981Formal_ThreeBoundEndpoint22TypeSplit_filteredPrefix_three
-- name    : Sensitivity213981Formal.ThreeBoundEndpoint22TypeSplit.filteredPrefix_three
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-27T01:32:04.148442+00:00
-- url     : https://prove2.me/theorems/ce5939d5-7e29-46d6-8c70-fdcb131e585a
-- title:
--   filtered Prefix three — Boolean sensitivity certificate
-- statement:
--   The following universally quantified assertion holds for the finite sets, Boolean families, tournament data, and profile coordinates defined in the imported interfaces. Each binder specifies the domain of its variable, and bracketed conditions specify finite or ordered structures.
--
--   $$
--   \forall \mathit{pref}:\operatorname{List}(\operatorname{Q3.Kind}),\quad \forall \mathit{lo}:\mathbb N,\quad \forall n:\mathbb N,\quad \bigl(\operatorname{Endpoint22TypeSplit.filteredPrefix}\bigl(\mathit{pref}, \mathit{lo}, \bigl(n+3\bigr)\bigr) = \operatorname{List.flatMap}\bigl(\left(a\mapsto \operatorname{ite}\bigl(\bigl(\mathit{lo} \le \operatorname{Q3.orderKey}\bigl(a\bigr)\bigr), \operatorname{List.flatMap}\bigl(\left(b\mapsto \operatorname{ite}\bigl(\bigl(\operatorname{Q3.orderKey}\bigl(a\bigr) \le \operatorname{Q3.orderKey}\bigl(b\bigr)\bigr), \operatorname{List.flatMap}\bigl(\left(c\mapsto \operatorname{ite}\bigl(\bigl(\operatorname{Q3.orderKey}\bigl(b\bigr) \le \operatorname{Q3.orderKey}\bigl(c\bigr)\bigr), \operatorname{Endpoint22TypeSplit.filteredPrefix}\bigl(\operatorname{HAppend.hAppend}\bigl(\mathit{pref}, \langle a,b,c\rangle\bigr), \operatorname{Q3.orderKey}\bigl(c\bigr), n\bigr), \langle\rangle\bigr)\right), \operatorname{List.finRange}\bigl(11\bigr)\bigr), \langle\rangle\bigr)\right), \operatorname{List.finRange}\bigl(11\bigr)\bigr), \langle\rangle\bigr)\right), \operatorname{List.finRange}\bigl(11\bigr)\bigr)\bigr)
--   $$
--
--   Here $\mathbb B=\{\mathsf{false},\mathsf{true}\}$; $\mathcal P_{\mathrm{fin}}(X)$ denotes the finite subsets of $X$. Named functions and predicates refer to their definitions in the cited source. This result supplies the corresponding filtered Prefix three step in the verified $22$-level sensitivity construction.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22TypeSplit.lean, lines 34–57.

import Definitions.Def_Sensitivity213981Formal_Endpoint22TypeSplit
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

theorem Sensitivity213981Formal.ThreeBoundEndpoint22TypeSplit.filteredPrefix_three :
∀ (pref : List.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind) (lo n : Nat),
  @Eq.{1} (List.{0} (List.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind))
    (Sensitivity213981Formal.ThreeBoundEndpoint22TypeSplit.filteredPrefix pref lo
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
        (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@List.flatMap.{0, 0} Sensitivity213981Formal.ThreeBoundQ3.Kind (List.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind)
      (fun (a : Sensitivity213981Formal.ThreeBoundQ3.Kind) =>
        @ite.{1} (List.{0} (List.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind))
          (@LE.le.{0} Nat instLENat lo (Sensitivity213981Formal.ThreeBoundQ3.orderKey a))
          (Nat.decLe lo (Sensitivity213981Formal.ThreeBoundQ3.orderKey a))
          (@List.flatMap.{0, 0} Sensitivity213981Formal.ThreeBoundQ3.Kind
            (List.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind)
            (fun (b : Sensitivity213981Formal.ThreeBoundQ3.Kind) =>
              @ite.{1} (List.{0} (List.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind))
                (@LE.le.{0} Nat instLENat (Sensitivity213981Formal.ThreeBoundQ3.orderKey a)
                  (Sensitivity213981Formal.ThreeBoundQ3.orderKey b))
                (Nat.decLe (Sensitivity213981Formal.ThreeBoundQ3.orderKey a)
                  (Sensitivity213981Formal.ThreeBoundQ3.orderKey b))
                (@List.flatMap.{0, 0} Sensitivity213981Formal.ThreeBoundQ3.Kind
                  (List.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind)
                  (fun (c : Sensitivity213981Formal.ThreeBoundQ3.Kind) =>
                    @ite.{1} (List.{0} (List.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind))
                      (@LE.le.{0} Nat instLENat (Sensitivity213981Formal.ThreeBoundQ3.orderKey b)
                        (Sensitivity213981Formal.ThreeBoundQ3.orderKey c))
                      (Nat.decLe (Sensitivity213981Formal.ThreeBoundQ3.orderKey b)
                        (Sensitivity213981Formal.ThreeBoundQ3.orderKey c))
                      (Sensitivity213981Formal.ThreeBoundEndpoint22TypeSplit.filteredPrefix
                        (@HAppend.hAppend.{0, 0, 0} (List.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind)
                          (List.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind)
                          (List.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind)
                          (@instHAppendOfAppend.{0} (List.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind)
                            (@List.instAppend.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind))
                          pref
                          (@List.cons.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind a
                            (@List.cons.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind b
                              (@List.cons.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind c
                                (@List.nil.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind)))))
                        (Sensitivity213981Formal.ThreeBoundQ3.orderKey c) n)
                      (@List.nil.{0} (List.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind)))
                  (List.finRange (@OfNat.ofNat.{0} Nat (nat_lit 11) (instOfNatNat (nat_lit 11)))))
                (@List.nil.{0} (List.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind)))
            (List.finRange (@OfNat.ofNat.{0} Nat (nat_lit 11) (instOfNatNat (nat_lit 11)))))
          (@List.nil.{0} (List.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind)))
      (List.finRange (@OfNat.ofNat.{0} Nat (nat_lit 11) (instOfNatNat (nat_lit 11))))) := by sorry
