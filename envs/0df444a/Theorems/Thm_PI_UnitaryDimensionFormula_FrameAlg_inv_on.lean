-- Prove2me | Theorems.Thm_PI_UnitaryDimensionFormula_FrameAlg_inv_on
-- name    : PI.UnitaryDimensionFormula.FrameAlg.inv_on
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T05:37:48.433216+00:00
-- url     : https://prove2.me/theorems/dccc0735-16c7-459e-9f8d-51f9d4a7d487
-- title:
--   Frame Alg: inv on
-- statement:
--   The Frame Alg construction uses the inv on property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/RankTwoDimensionFormula/IdxDcvAlg.lean#L94-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/RankTwoDimensionFormula/IdxDcvAlg.lean#L94-L98

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RankTwoDimensionFormula_IdxDcvAlg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open PI PI.UnitaryDimensionFormula PI.UnitaryDimensionFormula.FrameAlg
variable {A : Type} [CommRing A] {n : Type} [Fintype n] (σ : A →+* A) (J : Matrix n n A)
variable {r : ℕ}

theorem PI.UnitaryDimensionFormula.FrameAlg.inv_on {k : ℕ} (G : Matrix (Fin k) (Fin k) A) (ε y : A) (hy : ε * G.det * y = ε) :
    ((ε * y) • G.adjugate) * G = ε • (1 : Matrix (Fin k) (Fin k) A) := by sorry
