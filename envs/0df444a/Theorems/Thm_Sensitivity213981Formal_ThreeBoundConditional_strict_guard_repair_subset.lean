-- Prove2me | Theorems.Thm_Sensitivity213981Formal_ThreeBoundConditional_strict_guard_repair_subset
-- name    : Sensitivity213981Formal.ThreeBoundConditional.strict_guard_repair_subset
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-26T19:43:51.900241+00:00
-- url     : https://prove2.me/theorems/f5f72bd9-e927-439c-be28-a11713b14072
-- title:
--   strict guard repair subset — Boolean sensitivity certificate
-- statement:
--   The following universally quantified assertion holds for the finite sets, Boolean families, tournament data, and profile coordinates defined in the imported interfaces. Each binder specifies the domain of its variable, and bracketed conditions specify finite or ordered structures.
--
--   $$
--   \forall L:\mathcal U,\quad \forall I:\mathcal U,\quad \forall V:\mathcal U,\quad \bigl[\operatorname{LinearOrder}\bigl(L\bigr)\bigr]\;\bigl[\mathrm{finite}(I)\bigr]\;\bigl[\mathrm{finite}(V)\bigr]\;\forall S:\operatorname{Witness.Stage}\bigl(L, I, V\bigr),\quad \forall F:\left(L\to \left(\left(I\to \mathbb B\right)\to \mathbb B\right)\right),\quad \forall t:L,\quad \forall g:L,\quad \forall x:\left(V\times \mathbb B\times I\to \mathbb B\right),\quad \forall v:V,\quad \forall \mathit{w₀}:V,\quad \bigl(\forall c:\mathbb B,\quad \bigl(F\bigl(t, \operatorname{Witness.child}\bigl(x, v, c\bigr)\bigr) = \mathsf{true}\bigr)\Longrightarrow \bigl(\bigl(\operatorname{Conditional.guardFailures}\bigl(S, F, g, x, v\bigr) = \operatorname{Singleton.singleton}\bigl(\mathit{w₀}\bigr)\bigr)\Longrightarrow \bigl(\operatorname{Profiles.flipsTo}\bigl(\operatorname{Conditional.ordinaryRowBool}\bigl(S, F, t, g, 0, v\bigr), \mathsf{true}, x\bigr) \le \operatorname{Positive.liftBits}\bigl(\mathit{w₀}, \operatorname{Stage.label}\bigl(S, v, \mathit{w₀}\bigr), \operatorname{Profiles.flipsTo}\bigl(F\bigl(g\bigr), \mathsf{false}, \operatorname{Witness.child}\bigl(x, \mathit{w₀}, \operatorname{Stage.label}\bigl(S, v, \mathit{w₀}\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)
--   $$
--
--   Here $\mathbb B=\{\mathsf{false},\mathsf{true}\}$; $\mathcal P_{\mathrm{fin}}(X)$ denotes the finite subsets of $X$. Named functions and predicates refer to their definitions in the cited source. This result supplies the corresponding strict guard repair subset step in the verified $22$-level sensitivity construction.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; StrictUnion.lean, lines 254–274.

import Definitions.Def_Sensitivity213981Formal_ConditionalOrdinary
import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_Sensitivity213981Formal_StrictUnion
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem Sensitivity213981Formal.ThreeBoundConditional.strict_guard_repair_subset :
∀ {L I V : Type} [LinearOrder.{0} L] [inst : Fintype.{0} I] [inst_1 : Fintype.{0} V]
  (S : Sensitivity213981Formal.ThreeBoundWitness.Stage L I V) (F : L → (I → Bool) → Bool) (t g : L)
  (x : Prod.{0, 0} (Prod.{0, 0} V Bool) I → Bool) (v w₀ : V)
  (ht : ∀ (c : Bool), @Eq.{1} Bool (F t (@Sensitivity213981Formal.ThreeBoundWitness.child I V x v c)) Bool.true)
  (hg :
    @Eq.{1} (Finset.{0} V) (@Sensitivity213981Formal.ThreeBoundConditional.guardFailures L I V inst_1 S F g x v)
      (@Singleton.singleton.{0, 0} V (Finset.{0} V) (@Finset.instSingleton.{0} V) w₀)),
  @LE.le.{0} (Finset.{0} (Prod.{0, 0} (Prod.{0, 0} V Bool) I))
    (@Preorder.toLE.{0} (Finset.{0} (Prod.{0, 0} (Prod.{0, 0} V Bool) I))
      (@PartialOrder.toPreorder.{0} (Finset.{0} (Prod.{0, 0} (Prod.{0, 0} V Bool) I))
        (@Finset.instPartialOrder.{0} (Prod.{0, 0} (Prod.{0, 0} V Bool) I))))
    (@Sensitivity213981Formal.ThreeBoundProfiles.flipsTo (Prod.{0, 0} (Prod.{0, 0} V Bool) I)
      (@instFintypeProd.{0, 0} (Prod.{0, 0} V Bool) I (@instFintypeProd.{0, 0} V Bool inst_1 Bool.fintype) inst)
      (@Sensitivity213981Formal.ThreeBoundConditional.ordinaryRowBool L I V inst_1 S F t g
        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) v)
      Bool.true x)
    (@Sensitivity213981Formal.ThreeBoundPositive.liftBits I V w₀
      (@Sensitivity213981Formal.ThreeBoundWitness.Stage.label L I V S v w₀)
      (@Sensitivity213981Formal.ThreeBoundProfiles.flipsTo I inst (F g) Bool.false
        (@Sensitivity213981Formal.ThreeBoundWitness.child I V x w₀
          (@Sensitivity213981Formal.ThreeBoundWitness.Stage.label L I V S v w₀)))) := by sorry
