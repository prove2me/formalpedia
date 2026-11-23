-- Prove2me | Theorems.Thm_P2M_UpperTheory_Reformulated_B_AdicCompleteRootExistence_exists_root_of_dvd__8130b8fccf10
-- name    : P2M_UpperTheory_Reformulated_B_AdicCompleteRootExistence_exists_root_of_dvd__8130b8fccf10
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:15:48.78517+00:00
-- url     : https://prove2.me/theorems/13023714-ff6c-4e12-9fd6-043b9833923a
-- title:
--   P2 M Upper Theory Reformulated B Adic Complete Root Existence exists root of dvd  8130b8fccf10: P2 M Upper Theory Reformulated B Adic Complete Root Existence exists root of dvd  8130b8fccf10
-- statement:
--   The P2 M Upper Theory Reformulated B Adic Complete Root Existence exists root of dvd  8130b8fccf10 construction uses the P2 M Upper Theory Reformulated B Adic Complete Root Existence exists root of dvd  8130b8fccf10 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/ExistsRootOfAdicComplete.lean#L134-L152
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/ExistsRootOfAdicComplete.lean#L134-L152

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ExistsRootOfAdicComplete
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial

theorem P2M_UpperTheory_Reformulated_B_AdicCompleteRootExistence_exists_root_of_dvd__8130b8fccf10.{u_1} :
    ∀ {K : Type u_1} [inst : Field K] [inst_1 : ValuativeRel K] [inst_2 : TopologicalSpace K] [IsNonarchimedeanLocalField K]
      {ϖ : ↥(ValuativeRel.valuation K).integer},
      Irreducible ϖ →
        ∀ (f : Polynomial ↥(ValuativeRel.valuation K).integer) (a : ↥(ValuativeRel.valuation K).integer) (k : ℕ)
          (ε : (↥(ValuativeRel.valuation K).integer)ˣ),
          Polynomial.eval a
                ((Polynomial.derivative :
                    Polynomial ↥(ValuativeRel.valuation K).integer → Polynomial ↥(ValuativeRel.valuation K).integer)
                  f) =
              ϖ ^ k * (↑ε : ↥(ValuativeRel.valuation K).integer) →
            ϖ ^ ((2 : ℕ) * k + (1 : ℕ)) ∣ Polynomial.eval a f →
              ∃ (b : ↥(ValuativeRel.valuation K).integer),
                Polynomial.eval b f = (0 : ↥(ValuativeRel.valuation K).integer) ∧ ϖ ^ (k + (1 : ℕ)) ∣ b - a := by sorry

alias «UpperTheory».«Reformulated».«B».«AdicCompleteRootExistence».«exists_root_of_dvd».«» := P2M_UpperTheory_Reformulated_B_AdicCompleteRootExistence_exists_root_of_dvd__8130b8fccf10
