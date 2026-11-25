-- Prove2me | Theorems.Thm_SNumbers_prod_approximationNumber_le_detNumber
-- name    : SNumbers.prod_approximationNumber_le_detNumber
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T04:59:05.501995+00:00
-- url     : https://prove2.me/theorems/314c1007-a3c7-4407-9c2d-b109573e2a8b
-- title:
--   SNumbers: prod approximation Number le det Number
-- statement:
--   **Compression bound.** For contractions `A : ℓ₂ⁿ⁺¹ → X`,
--   `B : Y → ℓ₂ⁿ⁺¹` and `T := B∘S∘A`, the product of the top `n` approximation
--   numbers of `T` is at most `Δₙ(S)`: the diagonal factorisation
--   `B₁∘T∘A₁ = diag(a₀(T),…,aₙ(T))` through contractions
--   (`SVD.IsCompactOperator.diagonalFactorisation`), compressed to the first `n`
--   coordinates by `padFin`/`projFin`, realises `∏_{k<n} aₖ(T)` as an admissible
--   determinant for `Δₙ(S)`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/MaxDifference.lean#L292-L369
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/MaxDifference.lean#L292-L369

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

theorem SNumbers.prod_approximationNumber_le_detNumber (S : X →L[𝕜] Y) {n : ℕ}
    {A : EuclideanSpace 𝕜 (Fin (n + 1)) →L[𝕜] X}
    {B : Y →L[𝕜] EuclideanSpace 𝕜 (Fin (n + 1))}
    (hA : ‖A‖ ≤ 1) (hB : ‖B‖ ≤ 1) :
    ∏ i ∈ Finset.range n, approximationNumber (B.comp (S.comp A)) i
      ≤ detNumber S n := by sorry
