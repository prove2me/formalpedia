-- Prove2me | Theorems.Thm_Sensitivity213981Formal_ThreeBoundHighTypes_exists_kind
-- name    : Sensitivity213981Formal.ThreeBoundHighTypes.exists_kind
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-26T18:27:35.375079+00:00
-- url     : https://prove2.me/theorems/c8455e8e-6edb-416b-9e1d-e326b32149d5
-- title:
--   exists kind — Boolean sensitivity certificate
-- statement:
--   The following universally quantified assertion holds for the finite sets, Boolean families, tournament data, and profile coordinates defined in the imported interfaces. Each binder specifies the domain of its variable, and bracketed conditions specify finite or ordered structures.
--
--   $$
--   \forall q:\mathbb N,\quad \forall d:\mathbb N,\quad \forall P:\left(\mathbb N\to \mathrm{Prop}\right),\quad \forall G:\left(\mathbb N\to \mathrm{Prop}\right),\quad \bigl(\forall b:\mathbb N,\quad \bigl(P\bigl(b\bigr)\Longrightarrow \bigl(\bigl(b \le q\bigr) \land \bigl(d = b\bigr)\bigr)\bigr)\Longrightarrow \bigl(\forall b:\mathbb N,\quad \bigl(G\bigl(b\bigr)\Longrightarrow \bigl(\bigl(b \le q\bigr) \land \bigl(d = \bigl(b+1\bigr)\bigr)\bigr)\bigr)\Longrightarrow \bigl(\bigl(\exists b:\mathbb N,\quad P\bigl(b\bigr) \lor \exists b:\mathbb N,\quad G\bigl(b\bigr)\bigr)\Longrightarrow \exists k:\operatorname{HighTypes.Kind}\bigl(q\bigr),\quad \operatorname{HighTypes.OfKind}\bigl(q, P, G, k\bigr)\bigr)\bigr)\bigr)
--   $$
--
--   Here $\mathbb B=\{\mathsf{false},\mathsf{true}\}$; $\mathcal P_{\mathrm{fin}}(X)$ denotes the finite subsets of $X$. Named functions and predicates refer to their definitions in the cited source. This result supplies the corresponding exists kind step in the verified $22$-level sensitivity construction.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; HighTypeCore.lean, lines 27–69.

import Definitions.Def_Sensitivity213981Formal_HighTypeCore
import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Data.Fintype.Basic

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem Sensitivity213981Formal.ThreeBoundHighTypes.exists_kind :
∀ (q d : Nat) (P G : Nat → Prop) (hp : ∀ (b : Nat), P b → And (@LE.le.{0} Nat instLENat b q) (@Eq.{1} Nat d b))
  (hg :
    ∀ (b : Nat),
      G b →
        And (@LE.le.{0} Nat instLENat b q)
          (@Eq.{1} Nat d
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) b
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
  (h : Or (@Exists.{1} Nat fun (b : Nat) => P b) (@Exists.{1} Nat fun (b : Nat) => G b)),
  @Exists.{1} (Sensitivity213981Formal.ThreeBoundHighTypes.Kind q)
    fun (k : Sensitivity213981Formal.ThreeBoundHighTypes.Kind q) =>
    Sensitivity213981Formal.ThreeBoundHighTypes.OfKind q P G k := by sorry
