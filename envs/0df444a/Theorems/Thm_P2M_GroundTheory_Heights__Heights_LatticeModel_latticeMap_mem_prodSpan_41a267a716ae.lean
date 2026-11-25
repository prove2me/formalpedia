-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LatticeModel_latticeMap_mem_prodSpan_41a267a716ae
-- name    : P2M_GroundTheory_Heights__Heights_LatticeModel_latticeMap_mem_prodSpan_41a267a716ae
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T03:28:32.562157+00:00
-- url     : https://prove2.me/theorems/b07885de-396f-4842-b564-c8332d81c150
-- title:
--   P2 M Ground Theory Heights  Heights Lattice Model lattice Map mem prod Span 41a267a716ae: P2 M Ground Theory Heights  Heights Lattice Model lattice Map mem prod Span 41a267a716ae
-- statement:
--   The P2 M Ground Theory Heights  Heights Lattice Model lattice Map mem prod Span 41a267a716ae construction uses the P2 M Ground Theory Heights  Heights Lattice Model lattice Map mem prod Span 41a267a716ae property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/POneBlockModelB.lean#L76-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/POneBlockModelB.lean#L76-L86

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
variable {φ : Fin (N + 1) → Fin m → K}

theorem P2M_GroundTheory_Heights__Heights_LatticeModel_latticeMap_mem_prodSpan_41a267a716ae (hφ : IsDualBasis L φ) {d : ℕ}
    {f : MvPolynomial (Coord fun _ : Unit ↦ N) ℤ} (hf : f.IsHomogeneous d) : latticeMap φ f ∈ prodSpan L d := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LatticeModel».«latticeMap_mem_prodSpan» := P2M_GroundTheory_Heights__Heights_LatticeModel_latticeMap_mem_prodSpan_41a267a716ae
