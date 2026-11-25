-- Prove2me | Theorems.Thm_SNumbers_isCompactOperator_iff_tendsto_kolmogorovNumber
-- name    : SNumbers.isCompactOperator_iff_tendsto_kolmogorovNumber
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T05:23:53.929378+00:00
-- url     : https://prove2.me/theorems/fb615280-39df-5de0-9523-d90555b160cf
-- title:
--   SNumbers: is Compact Operator iff tendsto kolmogorov Number
-- statement:
--   **Compactness is measured by the Kolmogorov numbers**: for a complete target
--   space, `S` is a compact operator if and only if `dₙ(S) → 0`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/AddOns/Compact.lean#L252-L256
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/AddOns/Compact.lean#L252-L256

module
public import Definitions.Def_AddOns_Approximable
public import Definitions.Def_BasicResults_SVD
public import Definitions.Def_SNumbers_EntropyBounds
public import Definitions.Def_SNumbers_Uniqueness
public import Definitions.Def_AddOns_Compact
set_option autoImplicit true
@[expose] public section
public section
universe u
open Filter Topology
open scoped Cardinal
open SNumbers
variable {𝕜 : Type u} [RCLike 𝕜]
variable {X Y : Type u}
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]

theorem SNumbers.isCompactOperator_iff_tendsto_kolmogorovNumber [CompleteSpace Y]
    (S : X →L[𝕜] Y) :
    IsCompactOperator S ↔ Tendsto (kolmogorovNumber S) atTop (𝓝 0) := by sorry
