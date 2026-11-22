-- Prove2me | Theorems.Thm_P2M_Formalism_DivisionValues_PlaceSumConjugation_natCast_ne_zero__72e1bc708076
-- name    : P2M_Formalism_DivisionValues_PlaceSumConjugation_natCast_ne_zero__72e1bc708076
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:13:44.270423+00:00
-- url     : https://prove2.me/theorems/a5900438-ac0b-4cc0-b450-39da5e5312c5
-- title:
--   P2 M Formalism Division Values Place Sum Conjugation nat Cast ne zero  72e1bc708076: P2 M Formalism Division Values Place Sum Conjugation nat Cast ne zero  72e1bc708076
-- statement:
--   The P2 M Formalism Division Values Place Sum Conjugation nat Cast ne zero  72e1bc708076 construction uses the P2 M Formalism Division Values Place Sum Conjugation nat Cast ne zero  72e1bc708076 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/SecondComplementParameterBounds.lean#L18-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/SecondComplementParameterBounds.lean#L18-L19

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_Complement2Normaliser
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ProdFormula
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_SecondComplementParameterBounds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain Finset
noncomputable section
open Formalism Formalism.DivisionValues
open Formalism.DivisionValues.PlaceSumConjugation
variable {K : Type} [Field K] [NumberField K]

theorem P2M_Formalism_DivisionValues_PlaceSumConjugation_natCast_ne_zero__72e1bc708076 {g : ℕ} (hg : 0 < g) : (g : K) ≠ 0 := by sorry

alias «Formalism».«DivisionValues».«PlaceSumConjugation».«natCast_ne_zero'» := P2M_Formalism_DivisionValues_PlaceSumConjugation_natCast_ne_zero__72e1bc708076
