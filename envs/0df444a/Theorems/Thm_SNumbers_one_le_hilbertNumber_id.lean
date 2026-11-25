-- Prove2me | Theorems.Thm_SNumbers_one_le_hilbertNumber_id
-- name    : SNumbers.one_le_hilbertNumber_id
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:40:42.80788+00:00
-- url     : https://prove2.me/theorems/200df87d-bd37-4529-94ad-4f1eef75f171
-- title:
--   SNumbers: one le hilbert Number id
-- statement:
--   (S5, hard half) `1 ≤ h_n (id_{ℓ₂ⁿ⁺¹})`.
--
--   From a contractive section `A ∘ B = id_{ℓ₂ⁿ⁺¹}` (`exists_l2_section`) we get
--   `id = A ∘ (B ∘ A) ∘ B`, so the (S3) ideal property of the approximation
--   numbers and `aₙ(id_{ℓ₂ⁿ⁺¹}) = 1` (`approximationNumber_id_euclidean`) give
--   `1 ≤ aₙ(B ∘ A)`. The pair `(A, B)` is admissible for `hₙ(id)` with
--   `‖A‖, ‖B‖ ≤ 1`, so its ratio `aₙ(B ∘ A) / (‖B‖‖A‖) ≥ 1 ≤ hₙ(id)`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Hilbert.lean#L363-L404
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Hilbert.lean#L363-L404

module
public import Definitions.Def_SNumbers_Approximation
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.Normed.Module.HahnBanach
public import Definitions.Def_SNumbers_Hilbert
set_option autoImplicit true
@[expose] public section
public section
universe u
open scoped Cardinal
open ContinuousLinearMap
open SNumbers
variable {𝕜 : Type u} [RCLike 𝕜]
variable {X Y W Z : Type u}
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
variable [NormedAddCommGroup W] [NormedSpace 𝕜 W]
variable [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]

theorem SNumbers.one_le_hilbertNumber_id (n : ℕ) :
    1 ≤ hilbertNumber (ContinuousLinearMap.id 𝕜 (EuclideanSpace 𝕜 (Fin (n + 1)))) n := by sorry
