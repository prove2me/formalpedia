-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_CombCfBound_abs_cf_perm_755c477b2285
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_CombCfBound_abs_cf_perm_755c477b2285
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T08:04:49.931374+00:00
-- url     : https://prove2.me/theorems/6152bf35-a7f3-45cd-805c-825aa05715b0
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Comb Cf Bound abs cf perm 755c477b2285: P2 M Ground Theory Heights  Heights Rest Terms Comb Cf Bound abs cf perm 755c477b2285
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Comb Cf Bound abs cf perm 755c477b2285 construction uses the P2 M Ground Theory Heights  Heights Rest Terms Comb Cf Bound abs cf perm 755c477b2285 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PCombCfBound.lean#L13-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PCombCfBound.lean#L13-L16

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsComb
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PCombCfBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.RestTerms
open MvPolynomial Finset Equiv Comb
noncomputable section
open GroundTheory.Heights₂.Heights.RestTerms.CombCfBound

theorem P2M_GroundTheory_Heights__Heights_RestTerms_CombCfBound_abs_cf_perm_755c477b2285 {m : ℕ} {P : MvPolynomial (Fin m) ℚ} (hP : IsAlt P) (σ : Perm (Fin m))
    (v : Fin m → ℕ) : |cf (v ∘ σ.symm) P| = |cf v P| := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«CombCfBound».«abs_cf_perm» := P2M_GroundTheory_Heights__Heights_RestTerms_CombCfBound_abs_cf_perm_755c477b2285
