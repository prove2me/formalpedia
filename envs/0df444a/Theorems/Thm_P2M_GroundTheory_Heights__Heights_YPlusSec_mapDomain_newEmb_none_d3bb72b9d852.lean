-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_YPlusSec_mapDomain_newEmb_none_d3bb72b9d852
-- name    : P2M_GroundTheory_Heights__Heights_YPlusSec_mapDomain_newEmb_none_d3bb72b9d852
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T04:43:49.707812+00:00
-- url     : https://prove2.me/theorems/3a340377-bb40-43c7-be08-07f49f52f4c6
-- title:
--   P2 M Ground Theory Heights  Heights YPlus Sec map Domain new Emb none d3bb72b9d852: P2 M Ground Theory Heights  Heights YPlus Sec map Domain new Emb none d3bb72b9d852
-- statement:
--   The P2 M Ground Theory Heights  Heights YPlus Sec map Domain new Emb none d3bb72b9d852 construction uses the P2 M Ground Theory Heights  Heights YPlus Sec map Domain new Emb none d3bb72b9d852 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/PYPlusSec.lean#L21-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/PYPlusSec.lean#L21-L23

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

theorem P2M_GroundTheory_Heights__Heights_YPlusSec_mapDomain_newEmb_none_d3bb72b9d852 (m : (Σ _ : Unit, Fin (D.size + 1)) →₀ ℕ) (j : Fin (D.extSizes none + 1)) :
    Finsupp.mapDomain (newEmb D) m ⟨none, j⟩ = m ⟨(), j⟩ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«YPlusSec».«mapDomain_newEmb_none» := P2M_GroundTheory_Heights__Heights_YPlusSec_mapDomain_newEmb_none_d3bb72b9d852
