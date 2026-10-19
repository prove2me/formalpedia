-- Prove2me | Theorems.Thm_SoficGroups_KunRootedIndicatorCrossing_actionKernelUnitaryRepresentation_kerFun_one
-- name    : SoficGroups.KunRootedIndicatorCrossing.actionKernelUnitaryRepresentation_kerFun_one
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:25.142856+00:00
-- url     : https://prove2.me/theorems/2b98bf44-952d-4eb8-984b-bd4c33a273b9
-- title:
--   SoficGroups.KunRootedIndicatorCrossing.actionKernelUnitaryRepresentation_kerFun_one
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunRootedIndicatorCrossing
universe u
open Filter
open scoped BigOperators ComplexOrder InnerProductSpace Topology

theorem SoficGroups.KunRootedIndicatorCrossing.actionKernelUnitaryRepresentation_kerFun_one
    {G I : Type u} [Group G]
    (K : Matrix I I ℂ)
    [Fact (scalarOperatorKernel K).PosSemidef]
    (ρ : G →* Equiv.Perm I)
    (hinv : ∀ a i j, K (ρ a i) (ρ a j) = K i j)
    (a : G) (i : I) :
    actionKernelUnitaryRepresentation K ρ hinv a
      (RKHS.kerFun (RKHS.OfKernel (scalarOperatorKernel K)) i
        (1 : ℂ)) =
      RKHS.kerFun (RKHS.OfKernel (scalarOperatorKernel K))
        (ρ a i) (1 : ℂ) := by sorry
