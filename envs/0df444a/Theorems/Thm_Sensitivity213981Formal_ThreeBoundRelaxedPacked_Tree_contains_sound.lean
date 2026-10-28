-- Prove2me | Theorems.Thm_Sensitivity213981Formal_ThreeBoundRelaxedPacked_Tree_contains_sound
-- name    : Sensitivity213981Formal.ThreeBoundRelaxedPacked.Tree.contains_sound
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-27T01:52:55.132767+00:00
-- url     : https://prove2.me/theorems/0bba2790-e9b4-49c3-a305-2f2ff03ba2d5
-- title:
--   contains sound — Boolean sensitivity certificate
-- statement:
--   The following universally quantified assertion holds for the finite sets, Boolean families, tournament data, and profile coordinates defined in the imported interfaces. Each binder specifies the domain of its variable, and bracketed conditions specify finite or ordered structures.
--
--   $$
--   \forall t:\operatorname{RelaxedPacked.Tree},\quad \bigl(\bigl(\operatorname{Tree.checkKeys}\bigl(t\bigr) = \mathsf{true}\bigr)\Longrightarrow \forall \mathit{ss}:\operatorname{List}(\operatorname{Relaxed.State}),\quad \bigl(\bigl(|\mathit{ss}| \le 9\bigr)\Longrightarrow \bigl(\forall s:\operatorname{Relaxed.State},\quad \bigl(s\in \mathit{ss}\Longrightarrow \bigl(\operatorname{State.out}\bigl(s\bigr) \le 4\bigr)\bigr)\Longrightarrow \bigl(\forall s:\operatorname{Relaxed.State},\quad \bigl(s\in \mathit{ss}\Longrightarrow \bigl(\operatorname{State.incoming}\bigl(s\bigr) \le 8\bigr)\bigr)\Longrightarrow \bigl(\bigl(\operatorname{Tree.contains}\bigl(\operatorname{RelaxedPacked.fastKey}\bigl(\mathit{ss}\bigr), t\bigr) = \mathsf{true}\bigr)\Longrightarrow \operatorname{Relaxed.record}\bigl(\mathit{ss}\bigr)\in \operatorname{Tree.rows}\bigl(t\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)
--   $$
--
--   Here $\mathbb B=\{\mathsf{false},\mathsf{true}\}$; $\mathcal P_{\mathrm{fin}}(X)$ denotes the finite subsets of $X$. Named functions and predicates refer to their definitions in the cited source. This result supplies the corresponding contains sound step in the verified $22$-level sensitivity construction.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; RelaxedPackedTree.lean, lines 134–157.

import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_Sensitivity213981Formal_RelaxedPackedRecords
import Definitions.Def_Sensitivity213981Formal_RelaxedPackedTreeData
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
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Prod.Lex
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem Sensitivity213981Formal.ThreeBoundRelaxedPacked.Tree.contains_sound :
∀ (t : Sensitivity213981Formal.ThreeBoundRelaxedPacked.Tree)
  (hk : @Eq.{1} Bool (Sensitivity213981Formal.ThreeBoundRelaxedPacked.Tree.checkKeys t) Bool.true)
  (ss : List.{0} Sensitivity213981Formal.ThreeBoundRelaxed.State)
  (hn :
    @LE.le.{0} Nat instLENat (@List.length.{0} Sensitivity213981Formal.ThreeBoundRelaxed.State ss)
      (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9))))
  (ho :
    ∀ (s : Sensitivity213981Formal.ThreeBoundRelaxed.State),
      @Membership.mem.{0, 0} Sensitivity213981Formal.ThreeBoundRelaxed.State
          (List.{0} Sensitivity213981Formal.ThreeBoundRelaxed.State)
          (@List.instMembership.{0} Sensitivity213981Formal.ThreeBoundRelaxed.State) ss s →
        @LE.le.{0} Nat instLENat (Sensitivity213981Formal.ThreeBoundRelaxed.State.out s)
          (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
  (hi :
    ∀ (s : Sensitivity213981Formal.ThreeBoundRelaxed.State),
      @Membership.mem.{0, 0} Sensitivity213981Formal.ThreeBoundRelaxed.State
          (List.{0} Sensitivity213981Formal.ThreeBoundRelaxed.State)
          (@List.instMembership.{0} Sensitivity213981Formal.ThreeBoundRelaxed.State) ss s →
        @LE.le.{0} Nat instLENat (Sensitivity213981Formal.ThreeBoundRelaxed.State.incoming s)
          (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))
  (h :
    @Eq.{1} Bool
      (Sensitivity213981Formal.ThreeBoundRelaxedPacked.Tree.contains
        (Sensitivity213981Formal.ThreeBoundRelaxedPacked.fastKey ss) t)
      Bool.true),
  @Membership.mem.{0, 0} (List.{0} Nat) (List.{0} (List.{0} Nat)) (@List.instMembership.{0} (List.{0} Nat))
    (Sensitivity213981Formal.ThreeBoundRelaxedPacked.Tree.rows t) (Sensitivity213981Formal.ThreeBoundRelaxed.record ss) := by sorry
