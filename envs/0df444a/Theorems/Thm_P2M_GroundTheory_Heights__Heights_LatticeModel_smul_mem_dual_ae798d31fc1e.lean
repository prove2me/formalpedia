-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LatticeModel_smul_mem_dual_ae798d31fc1e
-- name    : P2M_GroundTheory_Heights__Heights_LatticeModel_smul_mem_dual_ae798d31fc1e
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:28:55.586325+00:00
-- url     : https://prove2.me/theorems/95a28b2f-5fbe-42a5-ac63-fa062f1b0a49
-- title:
--   P2 M Ground Theory Heights  Heights Lattice Model smul mem dual ae798d31fc1e: P2 M Ground Theory Heights  Heights Lattice Model smul mem dual ae798d31fc1e
-- statement:
--   The P2 M Ground Theory Heights  Heights Lattice Model smul mem dual ae798d31fc1e construction uses the P2 M Ground Theory Heights  Heights Lattice Model smul mem dual ae798d31fc1e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/POneBlockModelB.lean#L68-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/POneBlockModelB.lean#L68-L72

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

theorem P2M_GroundTheory_Heights__Heights_LatticeModel_smul_mem_dual_ae798d31fc1e (c : 𝓞 K) {u : Fin m → K} (hu : u ∈ latticeDual L) :
    algebraMap (𝓞 K) K c • u ∈ latticeDual L := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LatticeModel».«smul_mem_dual» := P2M_GroundTheory_Heights__Heights_LatticeModel_smul_mem_dual_ae798d31fc1e
