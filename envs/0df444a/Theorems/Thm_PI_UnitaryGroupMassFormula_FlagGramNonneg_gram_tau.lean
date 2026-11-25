-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_FlagGramNonneg_gram_tau
-- name    : PI.UnitaryGroupMassFormula.FlagGramNonneg.gram_tau
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T05:39:08.170072+00:00
-- url     : https://prove2.me/theorems/d7c7d13b-ab3e-47bb-a528-9c1099ff4b6c
-- title:
--   Flag Gram Nonneg: gram tau
-- statement:
--   The Flag Gram Nonneg construction uses the gram tau property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FlagGramNonnegativity/ConjTMulMulApply.lean#L29-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FlagGramNonnegativity/ConjTMulMulApply.lean#L29-L35

import Definitions.Def_Formalism_PeriodIntegrals_FlagGramNonneg
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FlagGramNonnegativity_ConjTMulMulApply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix PI.FlagGramNonneg
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.FlagGramNonneg

theorem PI.UnitaryGroupMassFormula.FlagGramNonneg.gram_tau {E : Type} [Field E] [StarRing E] {V : Type} [AddCommGroup V] [Module E V]
    (hT : V →ₗ⋆[E] V →ₗ[E] E) {N : ℕ} (b : Module.Basis (Fin N) E V) (τ : E →+* ℂ)
    (hτ : ∀ a, τ (star a) = starRingEnd ℂ (τ a)) {ι : Type} (y : ι → V) (i j : ι) :
    ((Matrix.of fun n k => τ (b.repr (y k) n))ᴴ * ((PI.FlagGramNonneg.gram hT b).map τ) *
      (Matrix.of fun n k => τ (b.repr (y k) n))) i j = τ (hT (y i) (y j)) := by sorry
