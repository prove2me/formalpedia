-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ArithVariety_chartMonomial_mem_of_not_isLive_657d083a777f
-- name    : P2M_GroundTheory_Heights__Heights_ArithVariety_chartMonomial_mem_of_not_isLive_657d083a777f
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T00:16:04.28149+00:00
-- url     : https://prove2.me/theorems/0e22fd8f-a6b3-4dfd-9b4f-7c1c612aec07
-- title:
--   P2 M Ground Theory Heights  Heights Arith Variety chart Monomial mem of not is Live 657d083a777f: P2 M Ground Theory Heights  Heights Arith Variety chart Monomial mem of not is Live 657d083a777f
-- statement:
--   The P2 M Ground Theory Heights  Heights Arith Variety chart Monomial mem of not is Live 657d083a777f construction uses the P2 M Ground Theory Heights  Heights Arith Variety chart Monomial mem of not is Live 657d083a777f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/ChartMonomialMemOfNotIsLive.lean#L11-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/ChartMonomialMemOfNotIsLive.lean#L11-L18

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_ChartMonomialMemOfNotIsLive
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
open MvPolynomial
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}

theorem P2M_GroundTheory_Heights__Heights_ArithVariety_chartMonomial_mem_of_not_isLive_657d083a777f (P : ArithVariety n) {c : (k : ι) → Fin (n k + 1)}
    (hc : ¬ P.IsLive c) {d : ι → ℕ} (hd : ∀ k, 1 ≤ d k) : chartMonomial c d ∈ P.ideal := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ArithVariety».«chartMonomial_mem_of_not_isLive» := P2M_GroundTheory_Heights__Heights_ArithVariety_chartMonomial_mem_of_not_isLive_657d083a777f
