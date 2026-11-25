-- Prove2me | Theorems.Thm_PIW_AdelClassFin_svR_conj
-- name    : PIW.AdelClassFin.svR_conj
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T05:47:56.601802+00:00
-- url     : https://prove2.me/theorems/8c59b2bb-8945-429e-86f2-d969e78adb23
-- title:
--   Adel Class Fin: sv R conj
-- statement:
--   The Adel Class Fin construction uses the sv R conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicClassFiniteness/SuccessiveVectorReal.lean#L79-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicClassFiniteness/SuccessiveVectorReal.lean#L79-L86

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_PartShortOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_SuccessiveVectorReal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PIW PIW.AdelClassFin
open Formalism.UG NumberField Matrix
open scoped ComplexOrder
variable {E : Type} [Field E] [NumberField E] [StarRing E]

theorem PIW.AdelClassFin.svR_conj {m N : ℕ} (e : Fin N → Fin m → E) (H : (E →+* ℂ) → Matrix (Fin m) (Fin m) ℂ)
    (φ : E →+* ℂ) (hc : H (ComplexEmbedding.conjugate φ) = (H φ).map (starRingEnd ℂ)) :
    (svP e (ComplexEmbedding.conjugate φ))ᴴ * H (ComplexEmbedding.conjugate φ) *
        svP e (ComplexEmbedding.conjugate φ) = ((svP e φ)ᴴ * H φ * svP e φ).map (starRingEnd ℂ) := by sorry
