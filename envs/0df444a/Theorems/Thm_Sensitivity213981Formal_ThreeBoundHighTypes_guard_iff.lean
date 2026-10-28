-- Prove2me | Theorems.Thm_Sensitivity213981Formal_ThreeBoundHighTypes_guard_iff
-- name    : Sensitivity213981Formal.ThreeBoundHighTypes.guard_iff
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-26T18:27:21.964+00:00
-- url     : https://prove2.me/theorems/bbdaef86-886b-45ea-83cd-f53a838a4740
-- title:
--   guard iff — Boolean sensitivity certificate
-- statement:
--   The following universally quantified assertion holds for the finite sets, Boolean families, tournament data, and profile coordinates defined in the imported interfaces. Each binder specifies the domain of its variable, and bracketed conditions specify finite or ordered structures.
--
--   $$
--   \forall q:\mathbb N,\quad \forall d:\mathbb N,\quad \forall P:\left(\mathbb N\to \mathrm{Prop}\right),\quad \forall G:\left(\mathbb N\to \mathrm{Prop}\right),\quad \forall k:\operatorname{HighTypes.Kind}\bigl(q\bigr),\quad \bigl(\forall b:\mathbb N,\quad \bigl(P\bigl(b\bigr)\Longrightarrow \bigl(\bigl(b \le q\bigr) \land \bigl(d = b\bigr)\bigr)\bigr)\Longrightarrow \bigl(\forall b:\mathbb N,\quad \bigl(G\bigl(b\bigr)\Longrightarrow \bigl(\bigl(b \le q\bigr) \land \bigl(d = \bigl(b+1\bigr)\bigr)\bigr)\bigr)\Longrightarrow \bigl(\operatorname{HighTypes.OfKind}\bigl(q, P, G, k\bigr)\Longrightarrow \bigl(\exists b:\mathbb N,\quad G\bigl(b\bigr) \Longleftrightarrow \bigl(\operatorname{HighTypes.isGuard}\bigl(q, k\bigr) = \mathsf{true}\bigr)\bigr)\bigr)\bigr)\bigr)
--   $$
--
--   Here $\mathbb B=\{\mathsf{false},\mathsf{true}\}$; $\mathcal P_{\mathrm{fin}}(X)$ denotes the finite subsets of $X$. Named functions and predicates refer to their definitions in the cited source. This result supplies the corresponding guard iff step in the verified $22$-level sensitivity construction.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; HighTypeCore.lean, lines 95–112.

import Definitions.Def_Sensitivity213981Formal_HighTypeCore
import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Data.Fintype.Basic

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem Sensitivity213981Formal.ThreeBoundHighTypes.guard_iff :
∀ (q d : Nat) (P G : Nat → Prop) (k : Sensitivity213981Formal.ThreeBoundHighTypes.Kind q)
  (hp : ∀ (b : Nat), P b → And (@LE.le.{0} Nat instLENat b q) (@Eq.{1} Nat d b))
  (hg :
    ∀ (b : Nat),
      G b →
        And (@LE.le.{0} Nat instLENat b q)
          (@Eq.{1} Nat d
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) b
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
  (hk : Sensitivity213981Formal.ThreeBoundHighTypes.OfKind q P G k),
  Iff (@Exists.{1} Nat fun (b : Nat) => G b)
    (@Eq.{1} Bool (Sensitivity213981Formal.ThreeBoundHighTypes.isGuard q k) Bool.true) := by sorry
