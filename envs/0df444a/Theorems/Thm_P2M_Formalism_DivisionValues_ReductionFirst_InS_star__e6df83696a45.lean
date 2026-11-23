-- Prove2me | Theorems.Thm_P2M_Formalism_DivisionValues_ReductionFirst_InS_star__e6df83696a45
-- name    : P2M_Formalism_DivisionValues_ReductionFirst_InS_star__e6df83696a45
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:02:18.455399+00:00
-- url     : https://prove2.me/theorems/3994caa4-cbd9-4cab-b67d-bdd836a3daad
-- title:
--   P2 M Formalism Division Values Reduction First In S star  e6df83696a45: P2 M Formalism Division Values Reduction First In S star  e6df83696a45
-- statement:
--   The P2 M Formalism Division Values Reduction First In S star  e6df83696a45 construction uses the P2 M Formalism Division Values Reduction First In S star  e6df83696a45 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/ReductionLemmaFirst.lean#L51-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/ReductionLemmaFirst.lean#L51-L54

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_ProdFormula
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SelectionLemmas
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ReductionLemmaFirst
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain Matrix
open scoped Matrix
noncomputable section
open Formalism Formalism.DivisionValues
open Formalism.DivisionValues.ReductionFirst
variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem P2M_Formalism_DivisionValues_ReductionFirst_InS_star__e6df83696a45 {w : HeightOneSpectrum (𝓞 K)} {x : K} (h : InS w x) : InS w (star x) := by sorry

alias «Formalism».«DivisionValues».«ReductionFirst».«InS».«star'» := P2M_Formalism_DivisionValues_ReductionFirst_InS_star__e6df83696a45
