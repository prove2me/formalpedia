-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LatticeModel_prod_mem_prodSpan_0cba948c4940
-- name    : P2M_GroundTheory_Heights__Heights_LatticeModel_prod_mem_prodSpan_0cba948c4940
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T03:29:25.329982+00:00
-- url     : https://prove2.me/theorems/c87184e2-8ab1-43eb-86b2-da3ad529b779
-- title:
--   P2 M Ground Theory Heights  Heights Lattice Model prod mem prod Span 0cba948c4940: P2 M Ground Theory Heights  Heights Lattice Model prod mem prod Span 0cba948c4940
-- statement:
--   The P2 M Ground Theory Heights  Heights Lattice Model prod mem prod Span 0cba948c4940 construction uses the P2 M Ground Theory Heights  Heights Lattice Model prod mem prod Span 0cba948c4940 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/POneBlockModelB.lean#L58-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/POneBlockModelB.lean#L58-L66

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_POneBlockModelA
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_POneBlockModelB
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
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G
noncomputable section
set_option linter.unusedSectionVars false
open GroundTheory.Heights₂.Heights.LatticeModel
variable {K : Type} [Field K] [NumberField K] {m N : ℕ} {L : Submodule (𝓞 K) (Fin m → K)}

theorem P2M_GroundTheory_Heights__Heights_LatticeModel_prod_mem_prodSpan_0cba948c4940 {ι : Type*} (t : Finset ι) (g : ι → MvPolynomial (Fin m) K) (e : ι → ℕ)
    (h : ∀ i ∈ t, g i ∈ prodSpan L (e i)) : ∏ i ∈ t, g i ∈ prodSpan L (∑ i ∈ t, e i) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LatticeModel».«prod_mem_prodSpan» := P2M_GroundTheory_Heights__Heights_LatticeModel_prod_mem_prodSpan_0cba948c4940
