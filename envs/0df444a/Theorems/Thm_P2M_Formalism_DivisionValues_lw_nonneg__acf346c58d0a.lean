-- Prove2me | Theorems.Thm_P2M_Formalism_DivisionValues_lw_nonneg__acf346c58d0a
-- name    : P2M_Formalism_DivisionValues_lw_nonneg__acf346c58d0a
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:02:44.714105+00:00
-- url     : https://prove2.me/theorems/b3196e62-d4e1-4f3c-a3b8-6f800c0d535d
-- title:
--   P2 M Formalism Division Values lw nonneg  acf346c58d0a: P2 M Formalism Division Values lw nonneg  acf346c58d0a
-- statement:
--   The P2 M Formalism Division Values lw nonneg  acf346c58d0a construction uses the P2 M Formalism Division Values lw nonneg  acf346c58d0a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/BoundsChain.lean#L12-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/BoundsChain.lean#L12-L15

import Definitions.Def_Formalism_QuotientMetricDivisors_ProdFormula
import Definitions.Def_Formalism_QuotientMetricDivisors_BoundsChain
import Definitions.Def_Formalism_QuotientMetricDivisors_ReductionLemmaZero
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_BoundsSum
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_BoundsChain
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
noncomputable section
open Formalism Formalism.DivisionValues

theorem P2M_Formalism_DivisionValues_lw_nonneg__acf346c58d0a {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) :
    0 ≤ lw w := by sorry

alias «Formalism».«DivisionValues».«lw_nonneg'» := P2M_Formalism_DivisionValues_lw_nonneg__acf346c58d0a
