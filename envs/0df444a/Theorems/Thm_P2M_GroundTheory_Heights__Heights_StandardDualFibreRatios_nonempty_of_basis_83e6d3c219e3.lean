-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_StandardDualFibreRatios_nonempty_of_basis_83e6d3c219e3
-- name    : P2M_GroundTheory_Heights__Heights_StandardDualFibreRatios_nonempty_of_basis_83e6d3c219e3
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T04:39:56.96735+00:00
-- url     : https://prove2.me/theorems/4b64ddbe-1d61-4fa8-a80d-7b1b2827726e
-- title:
--   P2 M Ground Theory Heights  Heights Standard Dual Fibre Ratios nonempty of basis 83e6d3c219e3: P2 M Ground Theory Heights  Heights Standard Dual Fibre Ratios nonempty of basis 83e6d3c219e3
-- statement:
--   The P2 M Ground Theory Heights  Heights Standard Dual Fibre Ratios nonempty of basis 83e6d3c219e3 construction uses the P2 M Ground Theory Heights  Heights Standard Dual Fibre Ratios nonempty of basis 83e6d3c219e3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PDualStdFibreRatios.lean#L12-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PDualStdFibreRatios.lean#L12-L21

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_DualStdModelField
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualArithVar
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualStdFibreRatios
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
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.ChartRestriction.G.AI.I1 NumberField MvPolynomial
open GroundTheory.Heights₂.Heights.StandardDualFibreRatios

theorem P2M_GroundTheory_Heights__Heights_StandardDualFibreRatios_nonempty_of_basis_83e6d3c219e3 {K : Type} [Field K] [NumberField K] {i : ℕ} {F : HermLattice K i} {T : Type} [Fintype T]
    (b : Module.Basis T ℤ (dualLattice F)) (hi : 1 ≤ i) : Nonempty T := by sorry

alias «GroundTheory».«Heights₂».«Heights».«StandardDualFibreRatios».«nonempty_of_basis» := P2M_GroundTheory_Heights__Heights_StandardDualFibreRatios_nonempty_of_basis_83e6d3c219e3
