-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_EffectiveHS_JetOfMonomialSum_snoc_const_55250f806c20
-- name    : P2M_GroundTheory_Heights__Heights_EffectiveHS_JetOfMonomialSum_snoc_const_55250f806c20
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T03:17:10.114398+00:00
-- url     : https://prove2.me/theorems/817b221a-1669-4f3e-814b-f8631269a13f
-- title:
--   P2 M Ground Theory Heights  Heights Effective HS Jet Of Monomial Sum snoc const 55250f806c20: P2 M Ground Theory Heights  Heights Effective HS Jet Of Monomial Sum snoc const 55250f806c20
-- statement:
--   The P2 M Ground Theory Heights  Heights Effective HS Jet Of Monomial Sum snoc const 55250f806c20 construction uses the P2 M Ground Theory Heights  Heights Effective HS Jet Of Monomial Sum snoc const 55250f806c20 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/EffectiveHilbertSamuel/PJetOfMonomialSum.lean#L66-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/EffectiveHilbertSamuel/PJetOfMonomialSum.lean#L66-L69

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_EffectiveHilbertSamuel_JetOfMonomialSumStatement
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_EffectiveHilbertSamuel_PJetOfMonomialSum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.EffectiveHS
open GroundTheory.Heights₂.Heights.EffectiveHS.JetOfMonomialSum
open Filter Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {x : E}

theorem P2M_GroundTheory_Heights__Heights_EffectiveHS_JetOfMonomialSum_snoc_const_55250f806c20 {F : Type*} (k : ℕ) (w : F) :
    (Fin.snoc (fun _ : Fin k => w) w : Fin (k + 1) → F) = fun _ => w := by sorry

alias «GroundTheory».«Heights₂».«Heights».«EffectiveHS».«JetOfMonomialSum».«snoc_const» := P2M_GroundTheory_Heights__Heights_EffectiveHS_JetOfMonomialSum_snoc_const_55250f806c20
