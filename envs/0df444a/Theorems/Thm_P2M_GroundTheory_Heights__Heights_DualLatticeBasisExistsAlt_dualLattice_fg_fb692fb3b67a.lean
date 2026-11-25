-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_DualLatticeBasisExistsAlt_dualLattice_fg_fb692fb3b67a
-- name    : P2M_GroundTheory_Heights__Heights_DualLatticeBasisExistsAlt_dualLattice_fg_fb692fb3b67a
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:17:04.775384+00:00
-- url     : https://prove2.me/theorems/7be6db0b-c0cb-522b-8bf1-f2c516a3111a
-- title:
--   P2 M Ground Theory Heights  Heights Dual Lattice Basis Exists Alt dual Lattice fg fb692fb3b67a: P2 M Ground Theory Heights  Heights Dual Lattice Basis Exists Alt dual Lattice fg fb692fb3b67a
-- statement:
--   The P2 M Ground Theory Heights  Heights Dual Lattice Basis Exists Alt dual Lattice fg fb692fb3b67a construction uses the P2 M Ground Theory Heights  Heights Dual Lattice Basis Exists Alt dual Lattice fg fb692fb3b67a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PDualLatticeBasisExists.lean#L36-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PDualLatticeBasisExists.lean#L36-L66

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsLineDegreeDual
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualLatticeBasisExists
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
open Matrix NumberField
noncomputable section
open GroundTheory.Heights₂.Heights.DualLatticeBasisExistsAlt
variable {K : Type} [Field K] [NumberField K] {i : ℕ}

theorem P2M_GroundTheory_Heights__Heights_DualLatticeBasisExistsAlt_dualLattice_fg_fb692fb3b67a (F : HermLattice K i) : (dualLattice F).FG := by sorry

alias «GroundTheory».«Heights₂».«Heights».«DualLatticeBasisExistsAlt».«dualLattice_fg» := P2M_GroundTheory_Heights__Heights_DualLatticeBasisExistsAlt_dualLattice_fg_fb692fb3b67a
