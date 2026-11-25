-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LatticeModel_latticeForm_mem_prodSpan_one_cbb7b48e9694
-- name    : P2M_GroundTheory_Heights__Heights_LatticeModel_latticeForm_mem_prodSpan_one_cbb7b48e9694
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T03:28:05.616321+00:00
-- url     : https://prove2.me/theorems/e32372a6-8fae-4cca-ac1a-272344b8fe9b
-- title:
--   P2 M Ground Theory Heights  Heights Lattice Model lattice Form mem prod Span one cbb7b48e9694: P2 M Ground Theory Heights  Heights Lattice Model lattice Form mem prod Span one cbb7b48e9694
-- statement:
--   The P2 M Ground Theory Heights  Heights Lattice Model lattice Form mem prod Span one cbb7b48e9694 construction uses the P2 M Ground Theory Heights  Heights Lattice Model lattice Form mem prod Span one cbb7b48e9694 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/POneBlockModelB.lean#L23-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/POneBlockModelB.lean#L23-L25

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

theorem P2M_GroundTheory_Heights__Heights_LatticeModel_latticeForm_mem_prodSpan_one_cbb7b48e9694 {u : Fin m → K} (hu : u ∈ latticeDual L) :
    latticeForm u ∈ prodSpan L 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LatticeModel».«latticeForm_mem_prodSpan_one» := P2M_GroundTheory_Heights__Heights_LatticeModel_latticeForm_mem_prodSpan_one_cbb7b48e9694
