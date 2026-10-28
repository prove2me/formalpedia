-- Prove2me | Theorems.Thm_Sensitivity213981Formal_ThreeBoundRankMarkers_dominator_mismatch_cap
-- name    : Sensitivity213981Formal.ThreeBoundRankMarkers.dominator_mismatch_cap
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-26T18:37:37.251606+00:00
-- url     : https://prove2.me/theorems/6d1d6309-dd88-43d7-97e7-842148dcf00c
-- title:
--   dominator mismatch cap — Boolean sensitivity certificate
-- statement:
--   The following universally quantified assertion holds for the finite sets, Boolean families, tournament data, and profile coordinates defined in the imported interfaces. Each binder specifies the domain of its variable, and bracketed conditions specify finite or ordered structures.
--
--   $$
--   \forall V:\mathcal U,\quad \forall X:\mathcal U,\quad \bigl[\mathrm{finite}(V)\bigr]\;\forall R:\left(V\to \left(V\to \mathrm{Prop}\right)\right),\quad \bigl(\operatorname{TournamentHighRows.IsTournament}\bigl(R\bigr)\Longrightarrow \forall \mathit{ell}:\left(V\to \left(V\to \mathbb B\right)\right),\quad \forall \mathit{guard}:\left(X\to \mathrm{Prop}\right),\quad \forall \mathit{children}:\left(V\to \left(\mathbb B\to X\right)\right),\quad \forall A:\mathcal P_{\mathrm{fin}}(V),\quad \forall H:\mathcal P_{\mathrm{fin}}(V),\quad \forall M:\mathcal P_{\mathrm{fin}}(V),\quad \bigl(\operatorname{Disjoint}\bigl(A, H\bigr)\Longrightarrow \bigl(\bigl(M \le H\bigr)\Longrightarrow \forall \mathit{color}:\left(V\to \mathbb B\right),\quad \forall m:\mathbb N,\quad \forall a:\mathbb N,\quad \bigl(\bigl(|M| = m\bigr)\Longrightarrow \bigl(\operatorname{ResidualCaps.DominatorCardBound}\bigl(R, \mathit{ell}, m, a\bigr)\Longrightarrow \bigl(\forall w:V,\quad \bigl(w\in A\Longrightarrow \forall c:\mathbb B,\quad \bigl(\bigl(c \ne \mathit{color}\bigl(w\bigr)\bigr)\Longrightarrow \mathit{guard}\bigl(\mathit{children}\bigl(w, c\bigr)\bigr)\bigr)\bigr)\Longrightarrow \bigl(\forall w:V,\quad \bigl(w\in H\Longrightarrow \forall c:\mathbb B,\quad \mathit{guard}\bigl(\mathit{children}\bigl(w, c\bigr)\bigr)\bigr)\Longrightarrow \bigl(\forall v:V,\quad \bigl(v\in A\Longrightarrow \bigl(|\operatorname{TournamentHighRows.guardFailures}\bigl(R, \mathit{ell}, \mathit{guard}, \mathit{children}, v\bigr)| = 0\bigr)\bigr)\Longrightarrow \bigl(|A| \le \bigl(\bigl(a-1\bigr)+\sum_{v\in M} |\operatorname{CandidateCoherence.mismatch}\bigl(R, \mathit{ell}, A, \mathit{color}, v\bigr)|\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)
--   $$
--
--   Here $\mathbb B=\{\mathsf{false},\mathsf{true}\}$; $\mathcal P_{\mathrm{fin}}(X)$ denotes the finite subsets of $X$. Named functions and predicates refer to their definitions in the cited source. This result supplies the corresponding dominator mismatch cap step in the verified $22$-level sensitivity construction.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; RankMarkerCaps.lean, lines 16–45.

import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_ResidualCaps
import Definitions.Def_Sensitivity213981Formal_Supplement_CandidateCoherence
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
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Sort
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem Sensitivity213981Formal.ThreeBoundRankMarkers.dominator_mismatch_cap :
∀ {V X : Type} [inst : Fintype.{0} V] [inst_1 : DecidableEq.{1} V] (R : V → V → Prop)
  (hR : @Sensitivity213981Formal.TournamentHighRows.IsTournament V R) (ell : V → V → Bool) (guard : X → Prop)
  (children : V → Bool → X) (A H M : Finset.{0} V)
  (hdis : @Disjoint.{0} (Finset.{0} V) (@Finset.instPartialOrder.{0} V) (@Finset.instOrderBot.{0} V) A H)
  (hMH :
    @LE.le.{0} (Finset.{0} V)
      (@Preorder.toLE.{0} (Finset.{0} V) (@PartialOrder.toPreorder.{0} (Finset.{0} V) (@Finset.instPartialOrder.{0} V)))
      M H)
  (color : V → Bool) (m a : Nat) (hM : @Eq.{1} Nat (@Finset.card.{0} V M) m)
  (hcap : @Sensitivity213981Formal.ResidualCaps.DominatorCardBound V inst_1 R ell m a)
  (hpartner :
    ∀ (w : V),
      @Membership.mem.{0, 0} V (Finset.{0} V)
          (@SetLike.instMembership.{0, 0} (Finset.{0} V) V (@Finset.instSetLike.{0} V)) A w →
        ∀ (c : Bool), @Ne.{1} Bool c (color w) → guard (children w c))
  (hhigh :
    ∀ (w : V),
      @Membership.mem.{0, 0} V (Finset.{0} V)
          (@SetLike.instMembership.{0, 0} (Finset.{0} V) V (@Finset.instSetLike.{0} V)) H w →
        ∀ (c : Bool), guard (children w c))
  (hzero :
    ∀ (v : V),
      @Membership.mem.{0, 0} V (Finset.{0} V)
          (@SetLike.instMembership.{0, 0} (Finset.{0} V) V (@Finset.instSetLike.{0} V)) A v →
        @Eq.{1} Nat
          (@Finset.card.{0} V
            (@Sensitivity213981Formal.TournamentHighRows.guardFailures V X inst R ell guard children v))
          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))),
  @LE.le.{0} Nat instLENat (@Finset.card.{0} V A)
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
      (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) a
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@Finset.sum.{0, 0} V Nat Nat.instAddCommMonoid M fun (v : V) =>
        @Finset.card.{0} V (@Sensitivity213981Formal.CandidateCoherence.mismatch V R ell A color v))) := by sorry
