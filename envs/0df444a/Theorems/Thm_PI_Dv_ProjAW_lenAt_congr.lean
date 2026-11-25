-- Prove2me | Theorems.Thm_PI_Dv_ProjAW_lenAt_congr
-- name    : PI.Dv.ProjAW.lenAt_congr
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T05:28:05.424007+00:00
-- url     : https://prove2.me/theorems/8955e61a-2541-453f-9de8-fc5f37b54f20
-- title:
--   Proj AW: len At congr
-- statement:
--   The Proj AW construction uses the len At congr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LengthIndex/LenAtEqZero.lean#L124-L132
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LengthIndex/LenAtEqZero.lean#L124-L132

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_DivisionRowsRationalLattice
import Definitions.Def_Formalism_PeriodIntegrals_IdxCalc
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LengthIndex_LenAtEqZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.ProjAW
open NumberField IsDedekindDomain Formalism.BasicNotions
variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable {V W : Type} [AddCommGroup V] [Module (𝓞 K) V] [AddCommGroup W] [Module (𝓞 K) W]

theorem PI.Dv.ProjAW.lenAt_congr (w : HeightOneSpectrum (𝓞 K)) (M N : Submodule (𝓞 K) V) (M' N' : Submodule (𝓞 K) W)
    (φ : (↥M ⧸ N.comap M.subtype) ≃ₗ[𝓞 K] (↥M' ⧸ N'.comap M'.subtype)) :
    lenAt w M N = lenAt w M' N' := by sorry
