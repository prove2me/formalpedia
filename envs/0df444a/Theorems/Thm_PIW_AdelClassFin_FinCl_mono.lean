-- Prove2me | Theorems.Thm_PIW_AdelClassFin_FinCl_mono
-- name    : PIW.AdelClassFin.FinCl.mono
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T13:12:26.256589+00:00
-- url     : https://prove2.me/theorems/b444f0b4-7909-48d9-baae-66d90b307769
-- title:
--   Fin Cl: mono
-- statement:
--   The Fin Cl construction uses the mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicClassFiniteness/HformSelfStar.lean#L83-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicClassFiniteness/HformSelfStar.lean#L83-L86

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_StGenusOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_HformSelfStar
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
open Formalism.UG NumberField
open scoped Matrix
variable {E : Type} [Field E] [NumberField E] [StarRing E]

theorem PIW.AdelClassFin.FinCl.mono {m : ℕ} {S S' : Set (Matrix (Fin m) (Fin m) E × Submodule (𝓞 E) (Fin m → E))}
    (h : FinCl S') (hs : S ⊆ S') : FinCl S := by sorry
