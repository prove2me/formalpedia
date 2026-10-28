-- Prove2me | Theorems.Thm_Sensitivity213981Formal_ThreeBoundHighTypes_positivePrefix_iff
-- name    : Sensitivity213981Formal.ThreeBoundHighTypes.positivePrefix_iff
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-26T18:28:46.998615+00:00
-- url     : https://prove2.me/theorems/152e8dda-4135-4bea-9852-bffae77b2aad
-- title:
--   positive Prefix iff — Boolean sensitivity certificate
-- statement:
--   The following universally quantified assertion holds for the finite sets, Boolean families, tournament data, and profile coordinates defined in the imported interfaces. Each binder specifies the domain of its variable, and bracketed conditions specify finite or ordered structures.
--
--   $$
--   \forall q:\mathbb N,\quad \forall d:\mathbb N,\quad \forall b:\mathbb N,\quad \forall P:\left(\mathbb N\to \mathrm{Prop}\right),\quad \forall G:\left(\mathbb N\to \mathrm{Prop}\right),\quad \forall k:\operatorname{HighTypes.Kind}\bigl(q\bigr),\quad \bigl(\forall c:\mathbb N,\quad \bigl(P\bigl(c\bigr)\Longrightarrow \bigl(\bigl(c \le q\bigr) \land \bigl(d = c\bigr)\bigr)\bigr)\Longrightarrow \bigl(\forall c:\mathbb N,\quad \bigl(G\bigl(c\bigr)\Longrightarrow \bigl(\bigl(c \le q\bigr) \land \bigl(d = \bigl(c+1\bigr)\bigr)\bigr)\bigr)\Longrightarrow \bigl(\operatorname{HighTypes.OfKind}\bigl(q, P, G, k\bigr)\Longrightarrow \bigl(\exists c:\mathbb N,\quad \bigl(\bigl(c \le b\bigr) \land P\bigl(c\bigr)\bigr) \Longleftrightarrow \bigl(\operatorname{HighTypes.positivePrefix}\bigl(q, b, k\bigr) = \mathsf{true}\bigr)\bigr)\bigr)\bigr)\bigr)
--   $$
--
--   Here $\mathbb B=\{\mathsf{false},\mathsf{true}\}$; $\mathcal P_{\mathrm{fin}}(X)$ denotes the finite subsets of $X$. Named functions and predicates refer to their definitions in the cited source. This result supplies the corresponding positive Prefix iff step in the verified $22$-level sensitivity construction.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; HighTypeCore.lean, lines 114–146.

import Definitions.Def_Sensitivity213981Formal_HighTypeCore
import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Data.Fintype.Basic

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem Sensitivity213981Formal.ThreeBoundHighTypes.positivePrefix_iff :
∀ (q d b : Nat) (P G : Nat → Prop) (k : Sensitivity213981Formal.ThreeBoundHighTypes.Kind q)
  (hp : ∀ (c : Nat), P c → And (@LE.le.{0} Nat instLENat c q) (@Eq.{1} Nat d c))
  (hg :
    ∀ (c : Nat),
      G c →
        And (@LE.le.{0} Nat instLENat c q)
          (@Eq.{1} Nat d
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
  (hk : Sensitivity213981Formal.ThreeBoundHighTypes.OfKind q P G k),
  Iff (@Exists.{1} Nat fun (c : Nat) => And (@LE.le.{0} Nat instLENat c b) (P c))
    (@Eq.{1} Bool (Sensitivity213981Formal.ThreeBoundHighTypes.positivePrefix q b k) Bool.true) := by sorry
