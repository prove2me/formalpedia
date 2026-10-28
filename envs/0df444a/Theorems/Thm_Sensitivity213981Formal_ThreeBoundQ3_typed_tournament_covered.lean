-- Prove2me | Theorems.Thm_Sensitivity213981Formal_ThreeBoundQ3_typed_tournament_covered
-- name    : Sensitivity213981Formal.ThreeBoundQ3.typed_tournament_covered
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-27T01:32:20.142594+00:00
-- url     : https://prove2.me/theorems/afb68573-bc97-43f6-8b78-601a4a721f9d
-- title:
--   typed tournament covered — Boolean sensitivity certificate
-- statement:
--   The following universally quantified assertion holds for the finite sets, Boolean families, tournament data, and profile coordinates defined in the imported interfaces. Each binder specifies the domain of its variable, and bracketed conditions specify finite or ordered structures.
--
--   $$
--   \forall V:\mathcal U,\quad \bigl[\mathrm{finite}(V)\bigr]\;\forall R:\left(V\to \left(V\to \mathrm{Prop}\right)\right),\quad \bigl(\operatorname{TournamentHighRows.IsTournament}\bigl(R\bigr)\Longrightarrow \forall \mathit{tag}:\left(V\to \operatorname{Q3.Kind}\right),\quad \bigl(\bigl(\operatorname{Fintype.card}\bigl(V\bigr) \le 9\bigr)\Longrightarrow \bigl(\forall q:\{0,\ldots,4-1\},\quad \bigl(|\operatorname{Finset.filter}\bigl(\left(v\mapsto \bigl(\operatorname{Q3.positivePrefix}\bigl(q, \mathit{tag}\bigl(v\bigr)\bigr) = \mathsf{true}\bigr)\right), \operatorname{univ}_{V}\bigr)| \le \bigl(\bigl(2\cdot q\bigr)+1\bigr)\bigr)\Longrightarrow \bigl(\forall v:V,\quad \bigl(|\operatorname{Finset.filter}\bigl(R\bigl(v\bigr), \operatorname{univ}_{V}\bigr)| \le \operatorname{Q3.budget}\bigl(\mathit{tag}\bigl(v\bigr)\bigr)\bigr)\Longrightarrow \exists \mathit{ts}:\operatorname{List}(\operatorname{Q3.Kind}),\quad \exists \mathit{ds}:\operatorname{List}(\mathbb B),\quad \exists e:\operatorname{Equiv}\bigl(\{0,\ldots,|\mathit{ts}|-1\}, V\bigr),\quad \bigl(\operatorname{List.Pairwise}\bigl(\left(a\mapsto \left(b\mapsto \bigl(\operatorname{Q3.orderKey}\bigl(a\bigr) \le \operatorname{Q3.orderKey}\bigl(b\bigr)\bigr)\right)\right), \mathit{ts}\bigr) \land \bigl(\forall i:\{0,\ldots,|\mathit{ts}|-1\},\quad \bigl(\operatorname{List.get}\bigl(\mathit{ts}, i\bigr) = \mathit{tag}\bigl(\operatorname{DFunLike.coe}\bigl(e, i\bigr)\bigr)\bigr) \land \bigl(\bigl(\mathit{ds} = \operatorname{Q2.orientationBits}\bigl(\left(i\mapsto \left(j\mapsto R\bigl(\operatorname{DFunLike.coe}\bigl(e, i\bigr), \operatorname{DFunLike.coe}\bigl(e, j\bigr)\bigr)\right)\right)\bigr)\bigr) \land \operatorname{Q3.record}\bigl((\mathit{ts},\mathit{ds})\bigr)\in \operatorname{Q3.records}\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)
--   $$
--
--   Here $\mathbb B=\{\mathsf{false},\mathsf{true}\}$; $\mathcal P_{\mathrm{fin}}(X)$ denotes the finite subsets of $X$. Named functions and predicates refer to their definitions in the cited source. This result supplies the corresponding typed tournament covered step in the verified $22$-level sensitivity construction.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Q3EnumerationBridge.lean, lines 45–104.

import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_Sensitivity213981Formal_Q2EnumerationBridge
import Definitions.Def_Sensitivity213981Formal_Q3Enumeration
import Definitions.Def_Sensitivity213981Formal_TournamentHighRows
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Sort
import Mathlib.Data.Prod.Lex
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem Sensitivity213981Formal.ThreeBoundQ3.typed_tournament_covered :
∀ {V : Type} [inst : Fintype.{0} V] (R : V → V → Prop)
  (hR : @Sensitivity213981Formal.TournamentHighRows.IsTournament V R)
  (tag : V → Sensitivity213981Formal.ThreeBoundQ3.Kind)
  (hn :
    @LE.le.{0} Nat instLENat (@Fintype.card.{0} V inst) (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9))))
  (hp :
    ∀ (q : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))),
      @LE.le.{0} Nat instLENat
        (@Finset.card.{0} V
          (@Finset.filter.{0} V
            (fun (v : V) =>
              @Eq.{1} Bool
                (Sensitivity213981Formal.ThreeBoundQ3.positivePrefix
                  (@Fin.val (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) q) (tag v))
                Bool.true)
            (fun (a : V) =>
              instDecidableEqBool
                (Sensitivity213981Formal.ThreeBoundQ3.positivePrefix
                  (@Fin.val (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) q) (tag a))
                Bool.true)
            (@Finset.univ.{0} V inst)))
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
            (@Fin.val (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) q))
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (hb :
    ∀ (v : V),
      @LE.le.{0} Nat instLENat
        (@Finset.card.{0} V
          (@Finset.filter.{0} V (R v) (fun (a : V) => Classical.propDecidable (R v a)) (@Finset.univ.{0} V inst)))
        (Sensitivity213981Formal.ThreeBoundQ3.budget (tag v))),
  @Exists.{1} (List.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind)
    fun (ts : List.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind) =>
    @Exists.{1} (List.{0} Bool) fun (ds : List.{0} Bool) =>
      @Exists.{1} (Equiv.{1, 1} (Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts)) V)
        fun (e : Equiv.{1, 1} (Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts)) V) =>
        And
          (@List.Pairwise.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind
            (fun (a b : Sensitivity213981Formal.ThreeBoundQ3.Kind) =>
              @LE.le.{0} Nat instLENat (Sensitivity213981Formal.ThreeBoundQ3.orderKey a)
                (Sensitivity213981Formal.ThreeBoundQ3.orderKey b))
            ts)
          (And
            (∀ (i : Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts)),
              @Eq.{1} Sensitivity213981Formal.ThreeBoundQ3.Kind
                (@List.get.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts i)
                (tag
                  (@DFunLike.coe.{1, 1, 1}
                    (Equiv.{1, 1} (Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts)) V)
                    (Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts))
                    (fun (x : Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts)) => V)
                    (@EquivLike.toFunLike.{1, 1, 1}
                      (Equiv.{1, 1} (Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts)) V)
                      (Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts)) V
                      (@Equiv.instEquivLike.{1, 1} (Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts))
                        V))
                    e i)))
            (And
              (@Eq.{1} (List.{0} Bool) ds
                (@Sensitivity213981Formal.ThreeBoundQ2.orientationBits
                  (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts)
                  (fun (i j : Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts)) =>
                    R
                      (@DFunLike.coe.{1, 1, 1}
                        (Equiv.{1, 1} (Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts)) V)
                        (Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts))
                        (fun (x : Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts)) => V)
                        (@EquivLike.toFunLike.{1, 1, 1}
                          (Equiv.{1, 1} (Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts)) V)
                          (Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts)) V
                          (@Equiv.instEquivLike.{1, 1}
                            (Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts)) V))
                        e i)
                      (@DFunLike.coe.{1, 1, 1}
                        (Equiv.{1, 1} (Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts)) V)
                        (Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts))
                        (fun (x : Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts)) => V)
                        (@EquivLike.toFunLike.{1, 1, 1}
                          (Equiv.{1, 1} (Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts)) V)
                          (Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts)) V
                          (@Equiv.instEquivLike.{1, 1}
                            (Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts)) V))
                        e j))
                  fun (a b : Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts)) =>
                  Classical.propDecidable
                    (R
                      (@DFunLike.coe.{1, 1, 1}
                        (Equiv.{1, 1} (Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts)) V)
                        (Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts))
                        (fun (x : Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts)) => V)
                        (@EquivLike.toFunLike.{1, 1, 1}
                          (Equiv.{1, 1} (Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts)) V)
                          (Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts)) V
                          (@Equiv.instEquivLike.{1, 1}
                            (Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts)) V))
                        e a)
                      (@DFunLike.coe.{1, 1, 1}
                        (Equiv.{1, 1} (Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts)) V)
                        (Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts))
                        (fun (x : Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts)) => V)
                        (@EquivLike.toFunLike.{1, 1, 1}
                          (Equiv.{1, 1} (Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts)) V)
                          (Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts)) V
                          (@Equiv.instEquivLike.{1, 1}
                            (Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts)) V))
                        e b))))
              (@Membership.mem.{0, 0} (List.{0} Nat) (List.{0} (List.{0} Nat)) (@List.instMembership.{0} (List.{0} Nat))
                Sensitivity213981Formal.ThreeBoundQ3.records
                (Sensitivity213981Formal.ThreeBoundQ3.record
                  (@Prod.mk.{0, 0} (List.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind) (List.{0} Bool) ts ds))))) := by sorry
