-- Prove2me | Theorems.Thm_P2M_Formalism_EigenvalueLevelCeiling_intValuation_eq_exp__a0f6a2bc12ef
-- name    : P2M_Formalism_EigenvalueLevelCeiling_intValuation_eq_exp__a0f6a2bc12ef
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:02:40.052835+00:00
-- url     : https://prove2.me/theorems/9f85f332-5852-40d1-91c3-677f8f4827a2
-- title:
--   P2 M Formalism Eigenvalue Level Ceiling int Valuation eq exp  a0f6a2bc12ef: P2 M Formalism Eigenvalue Level Ceiling int Valuation eq exp  a0f6a2bc12ef
-- statement:
--   The P2 M Formalism Eigenvalue Level Ceiling int Valuation eq exp  a0f6a2bc12ef construction uses the P2 M Formalism Eigenvalue Level Ceiling int Valuation eq exp  a0f6a2bc12ef property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MirabolicMackeyTheory/MirabolicMackeyProofs/RamBasic.lean#L40-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MirabolicMackeyTheory/MirabolicMackeyProofs/RamBasic.lean#L40-L42

import Mathlib
import Definitions.Def_Formalism_MirabolicMackeyTheory_StatementT
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_BoundsChain
import Definitions.Def_Formalism_LogFactorialIndices_SignedSubspaceIndex_LogProductFormula
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_RamBasic
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
open Formalism Formalism.EigenvalueLevelCeiling
open Formalism.DivisionValues
variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem P2M_Formalism_EigenvalueLevelCeiling_intValuation_eq_exp__a0f6a2bc12ef (w : HeightOneSpectrum (𝓞 K)) (x : 𝓞 K) (hx : x ≠ 0) :
    w.intValuation x = WithZero.exp (-(vw w (x : K))) := by sorry

alias «Formalism».«EigenvalueLevelCeiling».«intValuation_eq_exp'» := P2M_Formalism_EigenvalueLevelCeiling_intValuation_eq_exp__a0f6a2bc12ef
