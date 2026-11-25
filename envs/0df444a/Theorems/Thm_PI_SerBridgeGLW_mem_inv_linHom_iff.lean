-- Prove2me | Theorems.Thm_PI_SerBridgeGLW_mem_inv_linHom_iff
-- name    : PI.SerBridgeGLW.mem_inv_linHom_iff
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T05:37:33.517082+00:00
-- url     : https://prove2.me/theorems/03e8d201-50a0-4350-bf25-6b9a72cc59a7
-- title:
--   Ser Bridge GLW: mem inv lin Hom iff
-- statement:
--   The Ser Bridge GLW construction uses the mem inv lin Hom iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IrreducibleCharacterSeries/FrobeniusSumFormula.lean#L117-L133
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IrreducibleCharacterSeries/FrobeniusSumFormula.lean#L117-L133

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IrreducibleCharacterSeries_IrrCharIff
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IrreducibleCharacterSeries_ConjugateCharacterFormula
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IrreducibleCharacterSeries_FrobeniusSumFormula
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory Formalism.IrreducibleCountingLemmas.TYPES
open PI PI.SerBridgeGLW

theorem PI.SerBridgeGLW.mem_inv_linHom_iff {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] (ρV : Representation ℂ G V) (ρW : Representation ℂ G W) (f : V →ₗ[ℂ] W) :
    f ∈ (Representation.linHom ρV ρW).invariants ↔ ∀ g, f ∘ₗ ρV g = ρW g ∘ₗ f := by sorry
