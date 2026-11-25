-- Prove2me | Theorems.Thm_SNumbers_norm_det_le_pow_norm
-- name    : SNumbers.norm_det_le_pow_norm
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T04:35:48.186799+00:00
-- url     : https://prove2.me/theorems/b6868a28-86f3-5b06-bbe8-5d2191c03cf4
-- title:
--   SNumbers: norm det le pow norm
-- statement:
--   **`|det T| ≤ ‖T‖ᵏ`** for an endomorphism `T` of `ℓ₂ᵏ`. For `k ≥ 1` this is
--   the identity `∏ᵢ aᵢ(T) = |det T|` (`prod_approximationNumber_eq_norm_det`)
--   together with `aᵢ(T) ≤ ‖T‖`; for `k = 0` both sides are `1`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/MaxDifference.lean#L167-L185
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/MaxDifference.lean#L167-L185

module
public import Definitions.Def_SNumbers_Inequalities
public import Definitions.Def_SNumbers_PiLpCoordinates
public import Definitions.Def_BasicResults_Determinant
public import Definitions.Def_BasicResults_SVD
public import Definitions.Def_SNumbers_MaxDifference
set_option autoImplicit true
@[expose] public section
public section
universe u
open ContinuousLinearMap
open scoped Pointwise
open SNumbers
variable {𝕜 : Type u} [RCLike 𝕜]
variable {X Y : Type u}
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]

theorem SNumbers.norm_det_le_pow_norm {k : ℕ}
    (T : EuclideanSpace 𝕜 (Fin k) →L[𝕜] EuclideanSpace 𝕜 (Fin k)) :
    ‖LinearMap.det (T : EuclideanSpace 𝕜 (Fin k) →ₗ[𝕜] EuclideanSpace 𝕜 (Fin k))‖
      ≤ ‖T‖ ^ k := by sorry
