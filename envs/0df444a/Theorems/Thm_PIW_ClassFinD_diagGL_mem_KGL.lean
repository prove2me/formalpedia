-- Prove2me | Theorems.Thm_PIW_ClassFinD_diagGL_mem_KGL
-- name    : PIW.ClassFinD.diagGL_mem_KGL
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T05:48:07.895809+00:00
-- url     : https://prove2.me/theorems/4c06a8c3-9476-4dce-8b7a-a31e82b063b7
-- title:
--   Class Fin D: diag GL mem KGL
-- statement:
--   The Class Fin D construction uses the diag GL mem KGL property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IdeleClassFiniteness/BorelGL.lean#L65-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IdeleClassFiniteness/BorelGL.lean#L65-L81

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdeleClassFiniteness_OhatCompact
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdeleClassFiniteness_BorelGL
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PIW PIW.ClassFinD
open NumberField IsDedekindDomain

theorem PIW.ClassFinD.diagGL_mem_KGL (F : Type) [Field F] [NumberField F] (n : ℕ) (e : Fin n → (FiniteAdeleRing (𝓞 F) F)ˣ)
    (h1 : ∀ i, (e i : FiniteAdeleRing (𝓞 F) F) ∈ Ohat F)
    (h2 : ∀ i, ((e i)⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ).val ∈ Ohat F) : diagGL n e ∈ KGL F n := by sorry
