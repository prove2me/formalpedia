-- Prove2me | Theorems.Thm_PI_VolSemiDirect_W_PG_Dat_coordS_L
-- name    : PI.VolSemiDirect.W.PG.Dat.coordS_L
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T13:48:23.530288+00:00
-- url     : https://prove2.me/theorems/f340bbc2-55d1-57f8-8ee2-f592712cb6a5
-- title:
--   Dat: coord S L
-- statement:
--   The Dat construction uses the coord S L property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SemidirectVolume/ReflectionFixesNormal.lean#L47-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SemidirectVolume/ReflectionFixesNormal.lean#L47-L56

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ModVec
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ReflectionFixesNormal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolSemiDirect PI.VolSemiDirect.W PI.VolSemiDirect.W.PG
open Formalism.UG
variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] {r : ℕ}
open PI.VolSemiDirect.W.PG.Dat
variable {D : Dat A n r}

theorem PI.VolSemiDirect.W.PG.Dat.coordS_L (H : D.Hyp) {w : Fin r → n → A} (hw : ∀ a, IsW D (w a)) (s : Fin r → Fin r → A)
    (a b : Fin r) : D.h (D.f a) (D.L w s (D.f b)) = s a b := by sorry
