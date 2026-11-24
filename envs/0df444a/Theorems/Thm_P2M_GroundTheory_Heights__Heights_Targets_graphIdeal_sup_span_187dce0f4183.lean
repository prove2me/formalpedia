-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_graphIdeal_sup_span_187dce0f4183
-- name    : P2M_GroundTheory_Heights__Heights_Targets_graphIdeal_sup_span_187dce0f4183
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:01:25.016438+00:00
-- url     : https://prove2.me/theorems/fcd70d4e-10d8-4f9f-ae6f-9cd55ffd7097
-- title:
--   P2 M Ground Theory Heights  Heights Targets graph Ideal sup span 187dce0f4183: P2 M Ground Theory Heights  Heights Targets graph Ideal sup span 187dce0f4183
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets graph Ideal sup span 187dce0f4183 construction uses the P2 M Ground Theory Heights  Heights Targets graph Ideal sup span 187dce0f4183 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/GraphIdeal.lean#L101-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/GraphIdeal.lean#L101-L111

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsCurrent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_GraphIdeal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets
open MvPolynomial
open GroundTheory.Heights₂.Heights.ComplexSets (zeroSet)
variable {n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_Targets_graphIdeal_sup_span_187dce0f4183 (J : Ideal (MvPolynomial (Fin n) ℂ)) (p : MvPolynomial (Fin n) ℂ) :
    graphIdeal J p ⊔ Ideal.span {X (Fin.last n)} = graphIdeal (J ⊔ Ideal.span {p}) p := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«graphIdeal_sup_span» := P2M_GroundTheory_Heights__Heights_Targets_graphIdeal_sup_span_187dce0f4183
