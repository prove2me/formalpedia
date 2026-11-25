-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IsolatedFibreOpenPoly_eval_graphSubst_322e395e1249
-- name    : P2M_GroundTheory_Heights__Heights_IsolatedFibreOpenPoly_eval_graphSubst_322e395e1249
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T03:45:22.737649+00:00
-- url     : https://prove2.me/theorems/ec0bde5a-0967-4a54-a0c2-95aaa9a9871a
-- title:
--   P2 M Ground Theory Heights  Heights Isolated Fibre Open Poly eval graph Subst 322e395e1249: P2 M Ground Theory Heights  Heights Isolated Fibre Open Poly eval graph Subst 322e395e1249
-- statement:
--   The P2 M Ground Theory Heights  Heights Isolated Fibre Open Poly eval graph Subst 322e395e1249 construction uses the P2 M Ground Theory Heights  Heights Isolated Fibre Open Poly eval graph Subst 322e395e1249 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PIsolatedFibreOpenPoly.lean#L49-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PIsolatedFibreOpenPoly.lean#L49-L59

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StIsolatedFibreOpen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StIsolatedFibreOpenPoly
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PIsolatedFibreOpenPoly
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial Topology Filter Matrix ComplexSets
noncomputable section
open GroundTheory.Heights₂.Heights.IsolatedFibreOpenPoly
variable {n d : ℕ}

theorem P2M_GroundTheory_Heights__Heights_IsolatedFibreOpenPoly_eval_graphSubst_322e395e1249 (p : Fin d → MvPolynomial (Fin n) ℂ) (x : Fin n → ℂ)
    (q : MvPolynomial (Fin (n + d)) ℂ) : eval x (graphSubst p q) = eval (graphPt p x) q := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IsolatedFibreOpenPoly».«eval_graphSubst» := P2M_GroundTheory_Heights__Heights_IsolatedFibreOpenPoly_eval_graphSubst_322e395e1249
