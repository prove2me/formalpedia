-- Prove2me | Theorems.Thm_PI_LowUniSplit_conj_apply
-- name    : PI.LowUniSplit.conj_apply
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T15:39:26.081976+00:00
-- url     : https://prove2.me/theorems/217f0905-29e7-4c09-a39d-605c8ca6a60d
-- title:
--   Low Uni Split: conj apply
-- statement:
--   The Low Uni Split construction uses the conj apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LowerUnipotentSplit/SecondFactorMemLowerTriangular.lean#L30-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LowerUnipotentSplit/SecondFactorMemLowerTriangular.lean#L30-L35

import Definitions.Def_Formalism_HermitianCurvature_FiniteOrderIntersectionInSmooth
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LowerUnipotentSplit_SecondFactorMemLowerTriangular
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open PI PI.LowUniSplit
open Formalism.FourierDecayAlt.C2
variable {m : ℕ}

theorem PI.LowUniSplit.conj_apply (w : Equiv.Perm (Fin m)) (d : Fin m → ℂ) (hd : ∀ a, d a ≠ 0)
    (l : Matrix (Fin m) (Fin m) ℂ) (a b : Fin m) :
    ((monoP w d)⁻¹ * l * monoP w d) a b = (d a)⁻¹ * l (w a) (w b) * d b := by sorry
