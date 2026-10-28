-- Prove2me | Theorems.Thm_Sensitivity213981Formal_ThreeBoundQ3ActualRecordFields_all_record_fields
-- name    : Sensitivity213981Formal.ThreeBoundQ3ActualRecordFields.all_record_fields
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-27T01:34:35.437152+00:00
-- url     : https://prove2.me/theorems/cae7fedf-39dc-4311-ae60-6d5a5ce76e33
-- title:
--   all record fields — Boolean sensitivity certificate
-- statement:
--   The following universally quantified assertion holds for the finite sets, Boolean families, tournament data, and profile coordinates defined in the imported interfaces. Each binder specifies the domain of its variable, and bracketed conditions specify finite or ordered structures.
--
--   $$
--   \prod_{V:\mathcal U} \left(\mathrm{finite}(V)\to \prod_{\mathit{ts}:\operatorname{List}(\operatorname{Q3.Kind})} \prod_{\mathit{ds}:\operatorname{List}(\mathbb B)} \prod_{H:\mathcal P_{\mathrm{fin}}(V)} \prod_{G:\mathcal P_{\mathrm{fin}}(V)} \prod_{\mathit{tag}:\left(V\to \operatorname{Q3.Kind}\right)} \prod_{R:\left(V\to \left(V\to \mathrm{Prop}\right)\right)} \left(\operatorname{TournamentHighRows.IsTournament}\bigl(R\bigr)\to \prod_{e:\operatorname{Equiv}\bigl(\{0,\ldots,|\mathit{ts}|-1\}, \operatorname{Subtype}\bigl(\left(x\mapsto x\in H\right)\bigr)\bigr)} \left(\forall k:\{0,\ldots,|\mathit{ts}|-1\},\quad \bigl(\operatorname{List.get}\bigl(\mathit{ts}, k\bigr) = \mathit{tag}\bigl(\operatorname{DFunLike.coe}\bigl(e, k\bigr)\bigr)\bigr)\to \left(\bigl(\mathit{ds} = \operatorname{Q2.orientationBits}\bigl(\left(k\mapsto \left(l\mapsto R\bigl(\operatorname{DFunLike.coe}\bigl(e, k\bigr), \operatorname{DFunLike.coe}\bigl(e, l\bigr)\bigr)\right)\right)\bigr)\bigr)\to \prod_{\mathit{hG}:\bigl(G = \operatorname{Finset.filter}\bigl(\left(w\mapsto \bigl(\operatorname{Q3.isGuard}\bigl(\mathit{tag}\bigl(w\bigr)\bigr) = \mathsf{true}\bigr)\right), H\bigr)\bigr)} \prod_{\mathit{count}:\left(V\to \mathbb N\right)} \prod_{\mathit{hc}:\forall w:V,\quad \bigl(w\in H\Longrightarrow \bigl(\mathit{count}\bigl(w\bigr) = \operatorname{Q3.budget}\bigl(\mathit{tag}\bigl(w\bigr)\bigr)\bigr)\bigr)} \left(\text{let }r=\operatorname{Numeric.recordOfList}\bigl(\operatorname{Q3.record}\bigl((\mathit{ts},\mathit{ds})\bigr)\bigr)\text{ in }\bigl(\forall \mathit{kind}:\operatorname{Q3.Kind},\quad \bigl(r\bigl(\mathit{kind}\bigr) = |\operatorname{Finset.filter}\bigl(\left(w\mapsto \bigl(\mathit{tag}\bigl(w\bigr) = \mathit{kind}\bigr)\right), H\bigr)|\bigr) \land \bigl(\bigl(r\bigl(11\bigr) = \sum_{w\in G} \bigl(\mathit{count}\bigl(w\bigr)-|\operatorname{Finset.filter}\bigl(R\bigl(w\bigr), H\bigr)|\bigr)\bigr) \land \bigl(\forall \mathit{kind}:\operatorname{Q3.Kind},\quad \forall \mathit{hits}:\{0,\ldots,2-1\},\quad \bigl(r\bigl(\bigl(\bigl(12+\bigl(2\cdot \mathit{kind}\bigr)\bigr)+\mathit{hits}\bigr)\bigr) = |\operatorname{Finset.filter}\bigl(\left(w\mapsto \bigl(\bigl(\mathit{tag}\bigl(w\bigr) = \mathit{kind}\bigr) \land \bigl(\operatorname{Min.min}\bigl(2, |\operatorname{Finset.filter}\bigl(\left(v\mapsto R\bigl(v, w\bigr)\right), G\bigr)|\bigr) = \bigl(\mathit{hits}+1\bigr)\bigr)\bigr)\right), H\bigr)|\bigr) \land \forall k:\{0,\ldots,7-1\},\quad \bigl(\bigl(\bigl(k+1\bigr) \le |H|\bigr)\Longrightarrow \bigl(r\bigl(\bigl(34+k\bigr)\bigr) = \operatorname{List.sum}\bigl(\operatorname{List.take}\bigl(\bigl(k+1\bigr), \operatorname{List.mergeSort}\bigl(\operatorname{List.map}\bigl(\left(w\mapsto \bigl(\mathit{count}\bigl(w\bigr)-|\operatorname{Finset.filter}\bigl(R\bigl(w\bigr), H\bigr)|\bigr)\right), \operatorname{Finset.toList}\bigl(H\bigr)\bigr), \left(\mathit{x1}\mapsto \left(\mathit{x2}\mapsto \operatorname{decide}(\bigl(\mathit{x1} \le \mathit{x2}\bigr))\right)\right)\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)\right)\right)\right)\right)\right)
--   $$
--
--   Here $\mathbb B=\{\mathsf{false},\mathsf{true}\}$; $\mathcal P_{\mathrm{fin}}(X)$ denotes the finite subsets of $X$. Named functions and predicates refer to their definitions in the cited source. This result supplies the corresponding all record fields step in the verified $22$-level sensitivity construction.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Q3ActualRecordFields.lean, lines 135–165.

import Definitions.Def_Sensitivity213981Formal_GlobalAccounting
import Definitions.Def_Sensitivity213981Formal_GradedCandidates
import Definitions.Def_Sensitivity213981Formal_HeadCostExpressions
import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_Sensitivity213981Formal_Q2EnumerationBridge
import Definitions.Def_Sensitivity213981Formal_Q2RawExpressions
import Definitions.Def_Sensitivity213981Formal_Q3RecordFields
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
import Mathlib.Data.Finset.Powerset
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
import Mathlib.Data.Prod.Lex
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem Sensitivity213981Formal.ThreeBoundQ3ActualRecordFields.all_record_fields :
∀ {V : Type} [Fintype.{0} V] (ts : List.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind) (ds : List.{0} Bool)
  (H G : Finset.{0} V) (tag : V → Sensitivity213981Formal.ThreeBoundQ3.Kind) (R : V → V → Prop)
  (hR : @Sensitivity213981Formal.TournamentHighRows.IsTournament V R)
  (e :
    Equiv.{1, 1} (Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts))
      (@Subtype.{1} V fun (x : V) =>
        @Membership.mem.{0, 0} V (Finset.{0} V)
          (@SetLike.instMembership.{0, 0} (Finset.{0} V) V (@Finset.instSetLike.{0} V)) H x))
  (hget :
    ∀ (k : Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts)),
      @Eq.{1} Sensitivity213981Formal.ThreeBoundQ3.Kind (@List.get.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts k)
        (tag
          (@Subtype.val.{1} V
            (fun (x : V) =>
              @Membership.mem.{0, 0} V (Finset.{0} V)
                (@SetLike.instMembership.{0, 0} (Finset.{0} V) V (@Finset.instSetLike.{0} V)) H x)
            (@DFunLike.coe.{1, 1, 1}
              (Equiv.{1, 1} (Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts))
                (@Subtype.{1} V fun (x : V) =>
                  @Membership.mem.{0, 0} V (Finset.{0} V)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} V) V (@Finset.instSetLike.{0} V)) H x))
              (Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts))
              (fun (x : Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts)) =>
                @Subtype.{1} V fun (x : V) =>
                  @Membership.mem.{0, 0} V (Finset.{0} V)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} V) V (@Finset.instSetLike.{0} V)) H x)
              (@EquivLike.toFunLike.{1, 1, 1}
                (Equiv.{1, 1} (Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts))
                  (@Subtype.{1} V fun (x : V) =>
                    @Membership.mem.{0, 0} V (Finset.{0} V)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} V) V (@Finset.instSetLike.{0} V)) H x))
                (Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts))
                (@Subtype.{1} V fun (x : V) =>
                  @Membership.mem.{0, 0} V (Finset.{0} V)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} V) V (@Finset.instSetLike.{0} V)) H x)
                (@Equiv.instEquivLike.{1, 1} (Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts))
                  (@Subtype.{1} V fun (x : V) =>
                    @Membership.mem.{0, 0} V (Finset.{0} V)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} V) V (@Finset.instSetLike.{0} V)) H x)))
              e k))))
  (hdirs :
    @Eq.{1} (List.{0} Bool) ds
      (@Sensitivity213981Formal.ThreeBoundQ2.orientationBits
        (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts)
        (fun (k l : Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts)) =>
          R
            (@Subtype.val.{1} V
              (fun (x : V) =>
                @Membership.mem.{0, 0} V (Finset.{0} V)
                  (@SetLike.instMembership.{0, 0} (Finset.{0} V) V (@Finset.instSetLike.{0} V)) H x)
              (@DFunLike.coe.{1, 1, 1}
                (Equiv.{1, 1} (Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts))
                  (@Subtype.{1} V fun (x : V) =>
                    @Membership.mem.{0, 0} V (Finset.{0} V)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} V) V (@Finset.instSetLike.{0} V)) H x))
                (Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts))
                (fun (x : Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts)) =>
                  @Subtype.{1} V fun (x : V) =>
                    @Membership.mem.{0, 0} V (Finset.{0} V)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} V) V (@Finset.instSetLike.{0} V)) H x)
                (@EquivLike.toFunLike.{1, 1, 1}
                  (Equiv.{1, 1} (Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts))
                    (@Subtype.{1} V fun (x : V) =>
                      @Membership.mem.{0, 0} V (Finset.{0} V)
                        (@SetLike.instMembership.{0, 0} (Finset.{0} V) V (@Finset.instSetLike.{0} V)) H x))
                  (Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts))
                  (@Subtype.{1} V fun (x : V) =>
                    @Membership.mem.{0, 0} V (Finset.{0} V)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} V) V (@Finset.instSetLike.{0} V)) H x)
                  (@Equiv.instEquivLike.{1, 1} (Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts))
                    (@Subtype.{1} V fun (x : V) =>
                      @Membership.mem.{0, 0} V (Finset.{0} V)
                        (@SetLike.instMembership.{0, 0} (Finset.{0} V) V (@Finset.instSetLike.{0} V)) H x)))
                e k))
            (@Subtype.val.{1} V
              (fun (x : V) =>
                @Membership.mem.{0, 0} V (Finset.{0} V)
                  (@SetLike.instMembership.{0, 0} (Finset.{0} V) V (@Finset.instSetLike.{0} V)) H x)
              (@DFunLike.coe.{1, 1, 1}
                (Equiv.{1, 1} (Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts))
                  (@Subtype.{1} V fun (x : V) =>
                    @Membership.mem.{0, 0} V (Finset.{0} V)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} V) V (@Finset.instSetLike.{0} V)) H x))
                (Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts))
                (fun (x : Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts)) =>
                  @Subtype.{1} V fun (x : V) =>
                    @Membership.mem.{0, 0} V (Finset.{0} V)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} V) V (@Finset.instSetLike.{0} V)) H x)
                (@EquivLike.toFunLike.{1, 1, 1}
                  (Equiv.{1, 1} (Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts))
                    (@Subtype.{1} V fun (x : V) =>
                      @Membership.mem.{0, 0} V (Finset.{0} V)
                        (@SetLike.instMembership.{0, 0} (Finset.{0} V) V (@Finset.instSetLike.{0} V)) H x))
                  (Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts))
                  (@Subtype.{1} V fun (x : V) =>
                    @Membership.mem.{0, 0} V (Finset.{0} V)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} V) V (@Finset.instSetLike.{0} V)) H x)
                  (@Equiv.instEquivLike.{1, 1} (Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts))
                    (@Subtype.{1} V fun (x : V) =>
                      @Membership.mem.{0, 0} V (Finset.{0} V)
                        (@SetLike.instMembership.{0, 0} (Finset.{0} V) V (@Finset.instSetLike.{0} V)) H x)))
                e l)))
        fun (a b : Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts)) =>
        Classical.propDecidable
          (R
            (@Subtype.val.{1} V
              (fun (x : V) =>
                @Membership.mem.{0, 0} V (Finset.{0} V)
                  (@SetLike.instMembership.{0, 0} (Finset.{0} V) V (@Finset.instSetLike.{0} V)) H x)
              (@DFunLike.coe.{1, 1, 1}
                (Equiv.{1, 1} (Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts))
                  (@Subtype.{1} V fun (x : V) =>
                    @Membership.mem.{0, 0} V (Finset.{0} V)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} V) V (@Finset.instSetLike.{0} V)) H x))
                (Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts))
                (fun (x : Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts)) =>
                  @Subtype.{1} V fun (x : V) =>
                    @Membership.mem.{0, 0} V (Finset.{0} V)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} V) V (@Finset.instSetLike.{0} V)) H x)
                (@EquivLike.toFunLike.{1, 1, 1}
                  (Equiv.{1, 1} (Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts))
                    (@Subtype.{1} V fun (x : V) =>
                      @Membership.mem.{0, 0} V (Finset.{0} V)
                        (@SetLike.instMembership.{0, 0} (Finset.{0} V) V (@Finset.instSetLike.{0} V)) H x))
                  (Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts))
                  (@Subtype.{1} V fun (x : V) =>
                    @Membership.mem.{0, 0} V (Finset.{0} V)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} V) V (@Finset.instSetLike.{0} V)) H x)
                  (@Equiv.instEquivLike.{1, 1} (Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts))
                    (@Subtype.{1} V fun (x : V) =>
                      @Membership.mem.{0, 0} V (Finset.{0} V)
                        (@SetLike.instMembership.{0, 0} (Finset.{0} V) V (@Finset.instSetLike.{0} V)) H x)))
                e a))
            (@Subtype.val.{1} V
              (fun (x : V) =>
                @Membership.mem.{0, 0} V (Finset.{0} V)
                  (@SetLike.instMembership.{0, 0} (Finset.{0} V) V (@Finset.instSetLike.{0} V)) H x)
              (@DFunLike.coe.{1, 1, 1}
                (Equiv.{1, 1} (Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts))
                  (@Subtype.{1} V fun (x : V) =>
                    @Membership.mem.{0, 0} V (Finset.{0} V)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} V) V (@Finset.instSetLike.{0} V)) H x))
                (Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts))
                (fun (x : Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts)) =>
                  @Subtype.{1} V fun (x : V) =>
                    @Membership.mem.{0, 0} V (Finset.{0} V)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} V) V (@Finset.instSetLike.{0} V)) H x)
                (@EquivLike.toFunLike.{1, 1, 1}
                  (Equiv.{1, 1} (Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts))
                    (@Subtype.{1} V fun (x : V) =>
                      @Membership.mem.{0, 0} V (Finset.{0} V)
                        (@SetLike.instMembership.{0, 0} (Finset.{0} V) V (@Finset.instSetLike.{0} V)) H x))
                  (Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts))
                  (@Subtype.{1} V fun (x : V) =>
                    @Membership.mem.{0, 0} V (Finset.{0} V)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} V) V (@Finset.instSetLike.{0} V)) H x)
                  (@Equiv.instEquivLike.{1, 1} (Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts))
                    (@Subtype.{1} V fun (x : V) =>
                      @Membership.mem.{0, 0} V (Finset.{0} V)
                        (@SetLike.instMembership.{0, 0} (Finset.{0} V) V (@Finset.instSetLike.{0} V)) H x)))
                e b)))))
  (hG :
    @Eq.{1} (Finset.{0} V) G
      (@Finset.filter.{0} V
        (fun (w : V) => @Eq.{1} Bool (Sensitivity213981Formal.ThreeBoundQ3.isGuard (tag w)) Bool.true)
        (fun (a : V) => instDecidableEqBool (Sensitivity213981Formal.ThreeBoundQ3.isGuard (tag a)) Bool.true) H))
  (count : V → Nat)
  (hc :
    ∀ (w : V),
      @Membership.mem.{0, 0} V (Finset.{0} V)
          (@SetLike.instMembership.{0, 0} (Finset.{0} V) V (@Finset.instSetLike.{0} V)) H w →
        @Eq.{1} Nat (count w) (Sensitivity213981Formal.ThreeBoundQ3.budget (tag w))),
  have r : Sensitivity213981Formal.ThreeBoundNumeric.Q2Record :=
    Sensitivity213981Formal.ThreeBoundNumeric.recordOfList
      (Sensitivity213981Formal.ThreeBoundQ3.record
        (@Prod.mk.{0, 0} (List.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind) (List.{0} Bool) ts ds));
  And
    (∀ (kind : Sensitivity213981Formal.ThreeBoundQ3.Kind),
      @Eq.{1} Nat
        (r
          (@Fin.val
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            kind))
        (@Finset.card.{0} V
          (@Finset.filter.{0} V (fun (w : V) => @Eq.{1} Sensitivity213981Formal.ThreeBoundQ3.Kind (tag w) kind)
            (fun (a : V) =>
              instDecidableEqFin
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                    (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                (tag a) kind)
            H)))
    (And
      (@Eq.{1} Nat (r (@OfNat.ofNat.{0} Nat (nat_lit 11) (instOfNatNat (nat_lit 11))))
        (@Finset.sum.{0, 0} V Nat Nat.instAddCommMonoid G fun (w : V) =>
          @HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) (count w)
            (@Finset.card.{0} V (@Finset.filter.{0} V (R w) (fun (a : V) => Classical.propDecidable (R w a)) H))))
      (And
        (∀ (kind : Sensitivity213981Formal.ThreeBoundQ3.Kind)
          (hits : Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))),
          @Eq.{1} Nat
            (r
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 12) (instOfNatNat (nat_lit 12)))
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                    (@Fin.val
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                          (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                      kind)))
                (@Fin.val (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) hits)))
            (@Finset.card.{0} V
              (@Finset.filter.{0} V
                (fun (w : V) =>
                  And (@Eq.{1} Sensitivity213981Formal.ThreeBoundQ3.Kind (tag w) kind)
                    (@Eq.{1} Nat
                      (@Min.min.{0} Nat instMinNat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                        (@Finset.card.{0} V
                          (@Finset.filter.{0} V (fun (v : V) => R v w) (fun (a : V) => Classical.propDecidable (R a w))
                            G)))
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                        (@Fin.val (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) hits)
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                (fun (a : V) =>
                  @instDecidableAnd (@Eq.{1} Sensitivity213981Formal.ThreeBoundQ3.Kind (tag a) kind)
                    (@Eq.{1} Nat
                      (@Min.min.{0} Nat instMinNat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                        (@Finset.card.{0} V
                          (@Finset.filter.{0} V (fun (v : V) => R v a)
                            (fun (a_1 : V) => Classical.propDecidable (R a_1 a)) G)))
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                        (@Fin.val (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) hits)
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                    (instDecidableEqFin
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                          (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                      (tag a) kind)
                    (instDecidableEqNat
                      (@Min.min.{0} Nat instMinNat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                        (@Finset.card.{0} V
                          (@Finset.filter.{0} V (fun (v : V) => R v a)
                            (fun (a_1 : V) => Classical.propDecidable (R a_1 a)) G)))
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                        (@Fin.val (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) hits)
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                H)))
        (∀ (k : Fin (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))),
          @LE.le.{0} Nat instLENat
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@Fin.val (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))) k)
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              (@Finset.card.{0} V H) →
            @Eq.{1} Nat
              (r
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 34) (instOfNatNat (nat_lit 34)))
                  (@Fin.val (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))) k)))
              (@List.sum.{0} Nat instAddNat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass)
                (@List.take.{0} Nat
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (@Fin.val (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))) k)
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                  (@List.mergeSort.{0} Nat
                    (@List.map.{0, 0} V Nat
                      (fun (w : V) =>
                        @HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) (count w)
                          (@Finset.card.{0} V
                            (@Finset.filter.{0} V (R w) (fun (a : V) => Classical.propDecidable (R w a)) H)))
                      (@Finset.toList.{0} V H))
                    fun (x1 x2 : Nat) => @Decidable.decide (@LE.le.{0} Nat instLENat x1 x2) (Nat.decLe x1 x2))))))) := by sorry
