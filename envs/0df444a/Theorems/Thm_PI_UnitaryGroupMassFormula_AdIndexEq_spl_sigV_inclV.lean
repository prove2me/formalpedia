-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_AdIndexEq_spl_sigV_inclV
-- name    : PI.UnitaryGroupMassFormula.AdIndexEq.spl_sigV_inclV
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T14:10:32.638873+00:00
-- url     : https://prove2.me/theorems/dde76dca-693d-4408-b64b-3fd3d663587a
-- title:
--   Ad Index Eq: spl sig V incl V
-- statement:
--   The Ad Index Eq construction uses the spl sig V incl V property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicIndexEquality/LocSplitChiOf.lean#L23-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicIndexEquality/LocSplitChiOf.lean#L23-L27

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_SplitIso
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_SplitGL
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_LocSplitChiOf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.AdIndexEq
open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.MainNotions.S

theorem PI.UnitaryGroupMassFormula.AdIndexEq.spl_sigV_inclV (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) (x : I.E) :
    sigV I v (inclV I v x) = inclV I v (starRingEnd I.E x) := by sorry
