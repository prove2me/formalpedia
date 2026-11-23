-- Prove2me | Theorems.Thm_PI_VolSemiDirect_W_PG_Dat_reflection_fixes_normal
-- name    : PI.VolSemiDirect.W.PG.Dat.reflection_fixes_normal
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:49:25.168046+00:00
-- url     : https://prove2.me/theorems/1607e0cd-be05-4edb-a251-b389ea59948f
-- title:
--   Dat: reflection fixes normal
-- statement:
--   The Dat construction uses the reflection fixes normal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SemidirectVolume/ReflectionFixesNormal.lean#L21-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SemidirectVolume/ReflectionFixesNormal.lean#L21-L23

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

theorem PI.VolSemiDirect.W.PG.Dat.reflection_fixes_normal (H : D.Hyp) (w : Fin r → n → A) (s : Fin r → Fin r → A) : D.L w s D.z = D.z := by sorry
