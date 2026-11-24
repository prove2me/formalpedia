-- Prove2me | Theorems.Thm_PI_contractionsCovariant_iff
-- name    : PI.contractionsCovariant_iff
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T15:00:12.433152+00:00
-- url     : https://prove2.me/theorems/8359fb76-7c1c-4da7-877c-137a6e343dab
-- title:
--   PI: contractions Covariant iff
-- statement:
--   The PI construction uses the contractions Covariant iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/ContractionsCovariantIff.lean#L30-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/ContractionsCovariantIff.lean#L30-L43

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_PeriodIntegrals_ContractionsCovariantIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open PI
open Formalism.REAL Formalism.FourierDecayAlt.Q

theorem PI.contractionsCovariant_iff : ContractionsCovariant ↔ QnCovDet ∧ QnCovHat ∧ QnCovHat2 := by sorry
