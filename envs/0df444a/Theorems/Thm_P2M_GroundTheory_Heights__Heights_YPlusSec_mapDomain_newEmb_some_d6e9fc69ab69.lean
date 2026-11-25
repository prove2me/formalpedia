-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_YPlusSec_mapDomain_newEmb_some_d6e9fc69ab69
-- name    : P2M_GroundTheory_Heights__Heights_YPlusSec_mapDomain_newEmb_some_d6e9fc69ab69
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T04:43:56.390311+00:00
-- url     : https://prove2.me/theorems/cd210059-c1de-4a56-b2e2-2624ace39617
-- title:
--   P2 M Ground Theory Heights  Heights YPlus Sec map Domain new Emb some d6e9fc69ab69: P2 M Ground Theory Heights  Heights YPlus Sec map Domain new Emb some d6e9fc69ab69
-- statement:
--   The P2 M Ground Theory Heights  Heights YPlus Sec map Domain new Emb some d6e9fc69ab69 construction uses the P2 M Ground Theory Heights  Heights YPlus Sec map Domain new Emb some d6e9fc69ab69 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/PYPlusSec.lean#L25-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/PYPlusSec.lean#L25-L31

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_PYPlusSec
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
open MvPolynomial ReciprocityTheory.ChartRestriction.G
noncomputable section
open GroundTheory.Heights₂.Heights.YPlusSec
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ} {P : ArithVariety n} (D : AddBlockData P)

theorem P2M_GroundTheory_Heights__Heights_YPlusSec_mapDomain_newEmb_some_d6e9fc69ab69 (m : (Σ _ : Unit, Fin (D.size + 1)) →₀ ℕ) (k : ι)
    (i : Fin (D.extSizes (some k) + 1)) :
    Finsupp.mapDomain (newEmb D) m ⟨some k, i⟩ = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«YPlusSec».«mapDomain_newEmb_some» := P2M_GroundTheory_Heights__Heights_YPlusSec_mapDomain_newEmb_some_d6e9fc69ab69
