-- Prove2me | Theorems.Thm_PI_VolSemiDirect_W_PG_Dat_L_apply
-- name    : PI.VolSemiDirect.W.PG.Dat.L_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T00:18:24.058082+00:00
-- url     : https://prove2.me/theorems/79870757-4871-499b-bfb7-84cb23e08a79
-- title:
--   Dat: L apply
-- statement:
--   The Dat construction uses the L apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SemidirectVolume/ModVec.lean#L20-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SemidirectVolume/ModVec.lean#L20-L25

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_HermitianIsotropicProjComplement
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ModVec
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
variable (D : Dat A n r)

theorem PI.VolSemiDirect.W.PG.Dat.L_apply (w : Fin r → n → A) (s : Fin r → Fin r → A) (v : n → A) :
    D.L w s v = v + ∑ b, D.h (D.e b) v • (w b + ∑ a, s a b • D.e a) -
      ∑ a, D.h (w a) (D.pW v) • D.e a := by sorry
