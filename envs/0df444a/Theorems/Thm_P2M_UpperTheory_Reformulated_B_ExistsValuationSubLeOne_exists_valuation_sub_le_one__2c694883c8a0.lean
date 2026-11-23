-- Prove2me | Theorems.Thm_P2M_UpperTheory_Reformulated_B_ExistsValuationSubLeOne_exists_valuation_sub_le_one__2c694883c8a0
-- name    : P2M_UpperTheory_Reformulated_B_ExistsValuationSubLeOne_exists_valuation_sub_le_one__2c694883c8a0
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:32:15.745491+00:00
-- url     : https://prove2.me/theorems/e2e757a6-12a3-40ed-973f-a46b7858294c
-- title:
--   P2 M Upper Theory Reformulated B Exists Valuation Sub Le One exists valuation sub le one  2c694883c8a0: P2 M Upper Theory Reformulated B Exists Valuation Sub Le One exists valuation sub le one  2c6948
-- statement:
--   The P2 M Upper Theory Reformulated B Exists Valuation Sub Le One exists valuation sub le one  2c694883c8a0 construction uses the P2 M Upper Theory Reformulated B Exists Valuation Sub Le One exists valuation sub le one  2c694883c8a0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/ExistsValuationSubLeOne.lean#L3-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/ExistsValuationSubLeOne.lean#L3-L70

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ExistsValuationSubLeOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem P2M_UpperTheory_Reformulated_B_ExistsValuationSubLeOne_exists_valuation_sub_le_one__2c694883c8a0.{u_1, u_2} :
    ∀ {R : Type u_1} [inst : CommRing R] [inst_1 : IsDedekindDomain R] {K : Type u_2} [inst_2 : Field K]
    [inst_3 : Algebra R K] [inst_4 : IsFractionRing R K] (S : Finset (IsDedekindDomain.HeightOneSpectrum R))
    (x : IsDedekindDomain.HeightOneSpectrum R → K),
    ∃ (k : K),
      (∀ v ∈ S,
          (IsDedekindDomain.HeightOneSpectrum.valuation K v : K → WithZero (Multiplicative ℤ)) (k - x v) ≤
            (1 : WithZero (Multiplicative ℤ))) ∧
        ∀ v ∉ S,
          (IsDedekindDomain.HeightOneSpectrum.valuation K v : K → WithZero (Multiplicative ℤ)) k ≤
            (1 : WithZero (Multiplicative ℤ)) := by sorry

alias «UpperTheory».«Reformulated».«B».«ExistsValuationSubLeOne».«exists_valuation_sub_le_one».«» := P2M_UpperTheory_Reformulated_B_ExistsValuationSubLeOne_exists_valuation_sub_le_one__2c694883c8a0
