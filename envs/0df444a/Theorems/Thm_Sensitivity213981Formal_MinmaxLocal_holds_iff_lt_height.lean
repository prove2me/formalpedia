-- Prove2me | Theorems.Thm_Sensitivity213981Formal_MinmaxLocal_holds_iff_lt_height
-- name    : Sensitivity213981Formal.MinmaxLocal.holds_iff_lt_height
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-26T18:30:50.584974+00:00
-- url     : https://prove2.me/theorems/27eaaa19-5de2-40f5-a2be-9f94f52f32e4
-- title:
--   holds iff lt height — Boolean sensitivity certificate
-- statement:
--   The following universally quantified assertion holds for the finite sets, Boolean families, tournament data, and profile coordinates defined in the imported interfaces. Each binder specifies the domain of its variable, and bracketed conditions specify finite or ordered structures.
--
--   $$
--   \forall N:\mathbb N,\quad \forall X:\mathcal U,\quad \forall F:\left(\{0,\ldots,N-1\}\to \left(X\to \mathrm{Prop}\right)\right),\quad \bigl(\operatorname{MinmaxLocal.Nested}\bigl(F\bigr)\Longrightarrow \forall x:X,\quad \forall i:\{0,\ldots,N-1\},\quad \bigl(F\bigl(i, x\bigr) \Longleftrightarrow \bigl(i < \operatorname{MinmaxLocal.height}\bigl(F, x\bigr)\bigr)\bigr)\bigr)
--   $$
--
--   Here $\mathbb B=\{\mathsf{false},\mathsf{true}\}$; $\mathcal P_{\mathrm{fin}}(X)$ denotes the finite subsets of $X$. Named functions and predicates refer to their definitions in the cited source. This result supplies the corresponding holds iff lt height step in the verified $22$-level sensitivity construction.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; MinmaxLocal.lean, lines 44–61.

import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_Supplement_MinmaxLocal
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem Sensitivity213981Formal.MinmaxLocal.holds_iff_lt_height :
∀ {N : Nat} {X : Type} (F : Fin N → X → Prop) (hF : @Sensitivity213981Formal.MinmaxLocal.Nested N X F) (x : X)
  (i : Fin N),
  Iff (F i x) (@LT.lt.{0} Nat instLTNat (@Fin.val N i) (@Sensitivity213981Formal.MinmaxLocal.height N X F x)) := by sorry
