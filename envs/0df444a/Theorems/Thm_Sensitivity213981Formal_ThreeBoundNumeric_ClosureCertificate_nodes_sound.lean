-- Prove2me | Theorems.Thm_Sensitivity213981Formal_ThreeBoundNumeric_ClosureCertificate_nodes_sound
-- name    : Sensitivity213981Formal.ThreeBoundNumeric.ClosureCertificate.nodes_sound
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-26T20:55:12.425138+00:00
-- url     : https://prove2.me/theorems/57a6d3a1-3e13-454c-900d-07ecea86008b
-- title:
--   nodes sound — Boolean sensitivity certificate
-- statement:
--   The following universally quantified assertion holds for the finite sets, Boolean families, tournament data, and profile coordinates defined in the imported interfaces. Each binder specifies the domain of its variable, and bracketed conditions specify finite or ordered structures.
--
--   $$
--   \forall n:\mathbb N,\quad \forall I:\mathcal U,\quad \bigl[\mathrm{finite}(I)\bigr]\;\forall F:\left(\{0,\ldots,n-1\}\to \left(\left(I\to \mathbb B\right)\to \mathbb B\right)\right),\quad \bigl(\operatorname{Profiles.Nested}\bigl(F\bigr)\Longrightarrow \forall \mathit{input}:\operatorname{FullProfile.Profile}\bigl(n\bigr),\quad \forall \mathit{nodes}:\left(\mathbb N\to \operatorname{ClosureCertificate.Node}\bigl(n\bigr)\right),\quad \forall \mathit{count}:\mathbb N,\quad \forall c:\mathbb N,\quad \bigl(\operatorname{FullProfile.Upper}\bigl(F, \operatorname{FullProfile.scale}\bigl(c, \mathit{input}\bigr)\bigr)\Longrightarrow \bigl(\forall k:\mathbb N,\quad \bigl(\bigl(k < \mathit{count}\bigr)\Longrightarrow \bigl(\operatorname{ClosureCertificate.checkNode}\bigl(\mathit{input}, \mathit{nodes}, k\bigr) = \mathsf{true}\bigr)\bigr)\Longrightarrow \forall k:\mathbb N,\quad \bigl(\bigl(k < \mathit{count}\bigr)\Longrightarrow \operatorname{FullProfile.Sem}\bigl(F, \operatorname{Node.coord}\bigl(\mathit{nodes}\bigl(k\bigr)\bigr), \bigl(c\cdot \operatorname{Node.value}\bigl(\mathit{nodes}\bigl(k\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)
--   $$
--
--   Here $\mathbb B=\{\mathsf{false},\mathsf{true}\}$; $\mathcal P_{\mathrm{fin}}(X)$ denotes the finite subsets of $X$. Named functions and predicates refer to their definitions in the cited source. This result supplies the corresponding nodes sound step in the verified $22$-level sensitivity construction.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; ClosureCertificate.lean, lines 146–177.

import Definitions.Def_Sensitivity213981Formal_ClosureCertificate
import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_Sensitivity213981Formal_Supplement_FullProfileClosure
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.List.FinRange
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem Sensitivity213981Formal.ThreeBoundNumeric.ClosureCertificate.nodes_sound :
∀ {n : Nat} {I : Type} [inst : Fintype.{0} I] (F : Fin n → (I → Bool) → Bool)
  (hF :
    @Sensitivity213981Formal.ThreeBoundProfiles.Nested (Fin n) I
      (@PartialOrder.toPreorder.{0} (Fin n) (@Fin.instPartialOrder n)) F)
  (input : Sensitivity213981Formal.ThreeBoundFullProfile.Profile n)
  (nodes : Nat → Sensitivity213981Formal.ThreeBoundNumeric.ClosureCertificate.Node n) (count c : Nat)
  (hi :
    @Sensitivity213981Formal.ThreeBoundFullProfile.Upper n I inst F
      (@Sensitivity213981Formal.ThreeBoundFullProfile.scale n c input))
  (hn :
    ∀ (k : Nat),
      @LT.lt.{0} Nat instLTNat k count →
        @Eq.{1} Bool (@Sensitivity213981Formal.ThreeBoundNumeric.ClosureCertificate.checkNode n input nodes k)
          Bool.true)
  (k : Nat),
  @LT.lt.{0} Nat instLTNat k count →
    @Sensitivity213981Formal.ThreeBoundFullProfile.Sem n I inst F
      (@Sensitivity213981Formal.ThreeBoundNumeric.ClosureCertificate.Node.coord n (nodes k))
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) c
        (@Sensitivity213981Formal.ThreeBoundNumeric.ClosureCertificate.Node.value n (nodes k))) := by sorry
