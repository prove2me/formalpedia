-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_IrreducibleBasicOpenConnected_eval_linPoly_e958af14dbe7
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_IrreducibleBasicOpenConnected_eval_linPoly_e958af14dbe7
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:18:36.248969+00:00
-- url     : https://prove2.me/theorems/7d4bd3cf-b719-49b6-a499-661fac46ed58
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Irreducible Basic Open Connected eval lin Poly e958af14dbe7: P2 M Ground Theory Heights  Heights Hilbert Samuel Irreducible Basic Open Connected eval
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Irreducible Basic Open Connected eval lin Poly e958af14dbe7 construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Irreducible Basic Open Connected eval lin Poly e958af14dbe7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/IrreducibleConnected/BasicOpenSteps.lean#L24-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/IrreducibleConnected/BasicOpenSteps.lean#L24-L27

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFiniteMapOpen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_IrreducibleConnected_BasicOpenSteps
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial Filter Topology

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_IrreducibleBasicOpenConnected_eval_linPoly_e958af14dbe7 {n d : ℕ} (A : Matrix (Fin d) (Fin n) ℂ)
    (x : Fin n → ℂ) : (fun i => eval x (ComplexSets.linPoly A i)) = A.mulVec x := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«IrreducibleBasicOpenConnected».«eval_linPoly» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_IrreducibleBasicOpenConnected_eval_linPoly_e958af14dbe7
