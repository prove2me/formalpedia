-- Prove2me | Theorems.Thm_Sensitivity213981Formal_ThreeBoundPositive_guardBits_card_le
-- name    : Sensitivity213981Formal.ThreeBoundPositive.guardBits_card_le
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-26T18:25:09.969511+00:00
-- url     : https://prove2.me/theorems/e00905bb-2b00-451c-99be-f723eacf188f
-- title:
--   guard Bits card le — Boolean sensitivity certificate
-- statement:
--   The following universally quantified assertion holds for the finite sets, Boolean families, tournament data, and profile coordinates defined in the imported interfaces. Each binder specifies the domain of its variable, and bracketed conditions specify finite or ordered structures.
--
--   $$
--   \forall L:\mathcal U,\quad \forall I:\mathcal U,\quad \forall V:\mathcal U,\quad \bigl[\operatorname{Preorder}\bigl(L\bigr)\bigr]\;\bigl[\mathrm{finite}(I)\bigr]\;\bigl[\mathrm{finite}(V)\bigr]\;\forall S:\operatorname{Witness.Stage}\bigl(L, I, V\bigr),\quad \forall F:\left(L\to \left(\left(I\to \mathbb B\right)\to \mathbb B\right)\right),\quad \forall i:L,\quad \forall j:L,\quad \forall x:\left(V\times \mathbb B\times I\to \mathbb B\right),\quad \forall v:V,\quad \forall a:\mathbb N,\quad \bigl(\operatorname{Profiles.ABound}\bigl(F, \operatorname{Stage.guard}\bigl(S, j\bigr), \operatorname{Stage.guard}\bigl(S, i\bigr), a\bigr)\Longrightarrow \bigl(|\operatorname{Positive.guardBits}\bigl(S, F, i, j, x, v\bigr)| \le \bigl(\bigl(|\operatorname{Positive.outgoing}\bigl(S, v\bigr)|-|\operatorname{Witness.failed}\bigl(S, F, j, x, v\bigr)|\bigr)\cdot a\bigr)\bigr)\bigr)
--   $$
--
--   Here $\mathbb B=\{\mathsf{false},\mathsf{true}\}$; $\mathcal P_{\mathrm{fin}}(X)$ denotes the finite subsets of $X$. Named functions and predicates refer to their definitions in the cited source. This result supplies the corresponding guard Bits card le step in the verified $22$-level sensitivity construction.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; GradedPositiveBoundary.lean, lines 229–245.

import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_Supplement_GradedPositiveBoundary
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem Sensitivity213981Formal.ThreeBoundPositive.guardBits_card_le :
∀ {L I V : Type} [Preorder.{0} L] [inst : Fintype.{0} I] [inst_1 : Fintype.{0} V]
  (S : Sensitivity213981Formal.ThreeBoundWitness.Stage L I V) (F : L → (I → Bool) → Bool) (i j : L)
  (x : Prod.{0, 0} (Prod.{0, 0} V Bool) I → Bool) (v : V) (a : Nat)
  (ha :
    @Sensitivity213981Formal.ThreeBoundProfiles.ABound L I inst F
      (@Sensitivity213981Formal.ThreeBoundWitness.Stage.guard L I V S j)
      (@Sensitivity213981Formal.ThreeBoundWitness.Stage.guard L I V S i) a),
  @LE.le.{0} Nat instLENat
    (@Finset.card.{0} (Prod.{0, 0} (Prod.{0, 0} V Bool) I)
      (@Sensitivity213981Formal.ThreeBoundPositive.guardBits L I V inst inst_1 S F i j x v))
    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
      (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
        (@Finset.card.{0} V (@Sensitivity213981Formal.ThreeBoundPositive.outgoing L I V inst_1 S v))
        (@Finset.card.{0} V (@Sensitivity213981Formal.ThreeBoundWitness.failed L I V inst_1 S F j x v)))
      a) := by sorry
