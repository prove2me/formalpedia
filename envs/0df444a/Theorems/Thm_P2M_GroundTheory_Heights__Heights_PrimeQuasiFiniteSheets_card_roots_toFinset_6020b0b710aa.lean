-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_PrimeQuasiFiniteSheets_card_roots_toFinset_6020b0b710aa
-- name    : P2M_GroundTheory_Heights__Heights_PrimeQuasiFiniteSheets_card_roots_toFinset_6020b0b710aa
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T04:15:10.207791+00:00
-- url     : https://prove2.me/theorems/103d1e2d-3e55-4a03-9b6d-880d75c575d5
-- title:
--   P2 M Ground Theory Heights  Heights Prime Quasi Finite Sheets card roots to Finset 6020b0b710aa: P2 M Ground Theory Heights  Heights Prime Quasi Finite Sheets card roots to Finset 6020b0b710aa
-- statement:
--   The P2 M Ground Theory Heights  Heights Prime Quasi Finite Sheets card roots to Finset 6020b0b710aa construction uses the P2 M Ground Theory Heights  Heights Prime Quasi Finite Sheets card roots to Finset 6020b0b710aa property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PPrimeQuasiFiniteSheets.lean#L64-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PPrimeQuasiFiniteSheets.lean#L64-L65

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsPrimeQuasiFiniteSheets
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsFiniteFibresDimLe
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StDominantPrimitiveFibres
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSimpleRootBranch
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PPrimeQuasiFiniteSheets
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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
open GroundTheory.Heights₂.Heights.PrimeQuasiFiniteSheets
variable {n d : ℕ}

theorem P2M_GroundTheory_Heights__Heights_PrimeQuasiFiniteSheets_card_roots_toFinset_6020b0b710aa {p : Polynomial ℂ} (hp : p.Separable) : p.roots.toFinset.card = p.natDegree := by sorry

alias «GroundTheory».«Heights₂».«Heights».«PrimeQuasiFiniteSheets».«card_roots_toFinset» := P2M_GroundTheory_Heights__Heights_PrimeQuasiFiniteSheets_card_roots_toFinset_6020b0b710aa
