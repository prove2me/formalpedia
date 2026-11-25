-- Prove2me | Theorems.Thm_SNumbers_L1Linf_projinf_comp_incl_comp_emb1
-- name    : SNumbers.L1Linf.projinf_comp_incl_comp_emb1
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T05:14:42.418015+00:00
-- url     : https://prove2.me/theorems/230d79b9-a6d3-4a74-a14c-6e0318abf587
-- title:
--   L1 Linf: projinf comp incl comp emb1
-- statement:
--   The factorization `id_{ℓ₂ᵐ} = proj∞ ∘ I ∘ emb1`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Examples/IdentityL1Linfty.lean#L297-L303
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Examples/IdentityL1Linfty.lean#L297-L303

module
public import Definitions.Def_SNumbers_Gelfand
public import Definitions.Def_SNumbers_Hilbert
public import Definitions.Def_SNumbers_MaxDifference
public import Definitions.Def_BasicResults_LittleGrothendieck
public import Definitions.Def_BasicResults_SVD
public import Definitions.Def_AddOns_Approximable
public import Mathlib.Analysis.Normed.Lp.lpSpace
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.MetricSpace.Sequences
public import Definitions.Def_SNumbers_Examples_IdentityL1Linfty
set_option autoImplicit true
@[expose] public section
public section
open scoped ENNReal
open SNumbers SNumbers.L1Linf
variable {𝕜 : Type*} [RCLike 𝕜]

theorem SNumbers.L1Linf.projinf_comp_incl_comp_emb1 (m : ℕ) :
    (projinf m : Linf 𝕜 →L[𝕜] EuclideanSpace 𝕜 (Fin m)).comp
        ((incl : L1 𝕜 →L[𝕜] Linf 𝕜).comp (emb1 m))
      = ContinuousLinearMap.id 𝕜 (EuclideanSpace 𝕜 (Fin m)) := by sorry
