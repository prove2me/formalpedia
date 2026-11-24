-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LatticeModel_dehom_latticeForm_882e60645eed
-- name    : P2M_GroundTheory_Heights__Heights_LatticeModel_dehom_latticeForm_882e60645eed
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T01:35:04.219959+00:00
-- url     : https://prove2.me/theorems/cf84641d-bc32-4607-9f50-e0c2245254b4
-- title:
--   P2 M Ground Theory Heights  Heights Lattice Model dehom lattice Form 882e60645eed: P2 M Ground Theory Heights  Heights Lattice Model dehom lattice Form 882e60645eed
-- statement:
--   The P2 M Ground Theory Heights  Heights Lattice Model dehom lattice Form 882e60645eed construction uses the P2 M Ground Theory Heights  Heights Lattice Model dehom lattice Form 882e60645eed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/POneBlockModelA.lean#L184-L188
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/POneBlockModelA.lean#L184-L188

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_POneBlockModelA
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
variable {K : Type} [Field K] [NumberField K]
variable {m N : ℕ} {L : Submodule (𝓞 K) (Fin m → K)} {φ : Fin (N + 1) → Fin m → K}
variable {r : ℕ}

theorem P2M_GroundTheory_Heights__Heights_LatticeModel_dehom_latticeForm_882e60645eed (u : Fin (r + 1) → K) :
    dehom K r (latticeForm u) = algebraMap (MvPolynomial (Fin r) K) (LatticeField K r)
      (C (u 0) + ∑ j : Fin r, C (u j.succ) * X j) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LatticeModel».«dehom_latticeForm» := P2M_GroundTheory_Heights__Heights_LatticeModel_dehom_latticeForm_882e60645eed
