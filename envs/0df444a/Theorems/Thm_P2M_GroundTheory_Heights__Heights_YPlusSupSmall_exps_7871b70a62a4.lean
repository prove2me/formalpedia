-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_YPlusSupSmall_exps_7871b70a62a4
-- name    : P2M_GroundTheory_Heights__Heights_YPlusSupSmall_exps_7871b70a62a4
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:28:26.11681+00:00
-- url     : https://prove2.me/theorems/4e277038-21c2-4332-8589-15d69ea1907b
-- title:
--   P2 M Ground Theory Heights  Heights YPlus Sup Small exps 7871b70a62a4: P2 M Ground Theory Heights  Heights YPlus Sup Small exps 7871b70a62a4
-- statement:
--   The P2 M Ground Theory Heights  Heights YPlus Sup Small exps 7871b70a62a4 construction uses the P2 M Ground Theory Heights  Heights YPlus Sup Small exps 7871b70a62a4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/PYPlusSupSmall.lean#L23-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/PYPlusSupSmall.lean#L23-L31

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_PYPlusSupSmall
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
open GroundTheory.Heights₂.Heights.YPlusSupSmall
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ} {P : ArithVariety n} (D : AddBlockData P)

theorem P2M_GroundTheory_Heights__Heights_YPlusSupSmall_exps_7871b70a62a4 {τ : ℕ} {f : MvPolynomial (Coord D.extSizes) ℤ}
    (hf : Geo.IsMultiHomog (ι := blockIdx D.extSizes) f (Pi.single none τ)) {m : Coord D.extSizes →₀ ℕ}
    (hm : m ∈ f.support) : (∀ k i, m ⟨some k, i⟩ = 0) ∧ ∑ j, m ⟨none, j⟩ = τ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«YPlusSupSmall».«exps» := P2M_GroundTheory_Heights__Heights_YPlusSupSmall_exps_7871b70a62a4
