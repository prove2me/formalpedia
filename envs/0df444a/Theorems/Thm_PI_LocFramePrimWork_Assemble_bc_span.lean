-- Prove2me | Theorems.Thm_PI_LocFramePrimWork_Assemble_bc_span
-- name    : PI.LocFramePrimWork.Assemble_bc_span
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T05:35:21.443189+00:00
-- url     : https://prove2.me/theorems/1c060f1c-9b6f-4917-a380-6c707d36cb03
-- title:
--   Loc Frame Prim Work: Assemble bc span
-- statement:
--   The Loc Frame Prim Work construction uses the Assemble bc span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalPrimitiveFrame/Assemble.lean#L39-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalPrimitiveFrame/Assemble.lean#L39-L51

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalPrimitiveFrame_StepsTop
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalPrimitiveFrame_Assemble
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.LocFramePrimWork
open NumberField IsDedekindDomain PI.LocFramePrim
open scoped TensorProduct
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F)) {n : ℕ}

theorem PI.LocFramePrimWork.Assemble_bc_span (ψ : (Fin n → E) →ₗ[E] E) (Λ : Set (Fin n → E)) (S : Set E)
    (hS : ∀ l ∈ Λ, ψ l ∈ S) (x : Fin n → Fv F v ⊗[F] E) (hx : x ∈ latLoc (E := E) v Λ) :
    Assemble_bc v ψ x ∈ Submodule.span (v.adicCompletionIntegers F) (inclR (F := F) (Fv F v) '' S) := by sorry
