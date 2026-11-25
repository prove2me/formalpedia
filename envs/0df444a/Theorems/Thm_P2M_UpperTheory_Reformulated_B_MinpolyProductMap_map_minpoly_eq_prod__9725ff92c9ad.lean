-- Prove2me | Theorems.Thm_P2M_UpperTheory_Reformulated_B_MinpolyProductMap_map_minpoly_eq_prod__9725ff92c9ad
-- name    : P2M_UpperTheory_Reformulated_B_MinpolyProductMap_map_minpoly_eq_prod__9725ff92c9ad
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T13:43:48.045804+00:00
-- url     : https://prove2.me/theorems/f56ce56c-1ab3-5f60-a2e8-c73e0c11605a
-- title:
--   P2 M Upper Theory Reformulated B Minpoly Product Map map minpoly eq prod  9725ff92c9ad: P2 M Upper Theory Reformulated B Minpoly Product Map map minpoly eq prod  9725ff92c9ad
-- statement:
--   The P2 M Upper Theory Reformulated B Minpoly Product Map map minpoly eq prod  9725ff92c9ad construction uses the P2 M Upper Theory Reformulated B Minpoly Product Map map minpoly eq prod  9725ff92c9ad property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/MinpolyProductMap.lean#L25-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/MinpolyProductMap.lean#L25-L100

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Uniqueness
import Definitions.Def_GroundTheory_LocalFields_Interface
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_MinpolyProductMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped IntermediateField Algebra TensorProduct Matrix Pointwise NumberField Topology ContDiff NNReal ENNReal Polynomial DirectSum BigOperators InnerProductSpace Manifold

theorem P2M_UpperTheory_Reformulated_B_MinpolyProductMap_map_minpoly_eq_prod__9725ff92c9ad.{u_1, u_2} :
    ∀ {K : Type u_1} {L : Type u_2} [inst : Field K] [inst_1 : ValuativeRel K] [inst_2 : TopologicalSpace K]
      [inst_3 : IsNonarchimedeanLocalField K] [inst_4 : Field L] [inst_5 : ValuativeRel L] [inst_6 : TopologicalSpace L]
      [inst_7 : IsNonarchimedeanLocalField L] [inst_8 : Algebra K L] [inst_9 : ValuativeExtension K L]
      [inst_10 : FiniteDimensional K L] [IsGalois K L] {x : ↥(ValuativeRel.valuation L).integer},
      (↥(ValuativeRel.valuation K).integer)[x] = ⊤ →
        Polynomial.map (Algebra.algebraMap ↥(ValuativeRel.valuation K).integer ↥(ValuativeRel.valuation L).integer)
            (minpoly (↥(ValuativeRel.valuation K).integer) x) =
          ∏ σ : Gal(L/K),
            (Polynomial.X -
              (Polynomial.C : ↥(ValuativeRel.valuation L).integer → Polynomial ↥(ValuativeRel.valuation L).integer)
                (((GroundTheory.LocalField.integerAlgEquiv K L :
                               Gal(L/K) →
                                 ↥(ValuativeRel.valuation L).integer ≃ₐ[↥(ValuativeRel.valuation K).integer]
                                   ↥(ValuativeRel.valuation L).integer)
                      σ :
                    ↥(ValuativeRel.valuation L).integer → ↥(ValuativeRel.valuation L).integer)
                  x)) := by sorry

alias «UpperTheory».«Reformulated».«B».«MinpolyProductMap».«map_minpoly_eq_prod».«» := P2M_UpperTheory_Reformulated_B_MinpolyProductMap_map_minpoly_eq_prod__9725ff92c9ad
