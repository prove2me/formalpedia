-- Prove2me | Theorems.Thm_StochFictPlay_DiscreteChoice_argmax_firstOrder_strictConvex
-- name    : StochFictPlay.DiscreteChoice.argmax_firstOrder_strictConvex
-- status  : Disproved
-- author  : @junyihjy
-- created : 2026-10-01T17:18:17.591982+00:00
-- url     : https://prove2.me/theorems/e53a1359-56b4-4abf-b262-78f55924b9ca
-- title:
--   First-order characterization of the convex-conjugate argmax (Hofbauer–Sandholm 2002, Thm 2.1 FOC step)
-- statement:
--   Let V : (Fin n → ℝ) → ℝ be strictly convex and C¹ on an open set O, with injective gradient field. For payoffs π and y⋆ ∈ O, y⋆ maximizes y ↦ (∑ᵢ yᵢ πᵢ) − V(y) over O if and only if π = ∇V(y⋆) (coordinate-wise: πᵢ = V′(eᵢ)), and the maximizer is unique in O. This is the first-order-conditions step of the proof of Hofbauer–Sandholm (2002) Theorem 2.1: argmax_{y}(y·π − V(y)) is pinned down by π = ∇V(y⋆).
-- source:
--   Hofbauer & Sandholm (2002), On the Global Convergence of Stochastic Fictitious Play, Econometrica 70(6):2265–2294, proof of Theorem 2.1 (pp. 5–7): the FOC step — the argmax of y·π − V(y) is characterized by π = ∇V(y⋆). Bridge node #3 in ~/workspace/p2m_harness/stochfictplay_triage.md ('Named publish-candidate children'). Decomposition child of StochFictPlay.DiscreteChoice.exists_admissible_perturbation (Thm 2.1, Mission I: 8d9182ea-3ec4-465c-8532-7dce6b690d44).

import Mathlib

namespace StochFictPlay
namespace DiscreteChoice

/-- First-order (Fenchel--Young-adjacent) characterization of the convex-conjugate
argmax: the FOC step of the proof of Hofbauer--Sandholm (2002) Theorem 2.1.
For a strictly convex C¹ perturbation `V` on an open set `O` whose gradient
field is injective, `y_star ∈ O` maximizes `y ↦ (sum i, y i * π i) - V y` over `O`
iff the first-order condition `π = ∇V y_star` holds, and then `y_star` is the
unique maximizer in `O`. -/
theorem argmax_firstOrder_strictConvex {n : ℕ} (V : (Fin n → ℝ) → ℝ) (O : Set (Fin n → ℝ))
    (hO : IsOpen O) (hCV : StrictConvexOn ℝ O V)
    (π : Fin n → ℝ) (y_star : Fin n → ℝ) (hys : y_star ∈ O)
    (V' : (Fin n → ℝ) →L[ℝ] ℝ) (hV' : HasFDerivAt V V' y_star)
    (hinj : ∀ y₁ ∈ O, ∀ y₂ ∈ O, ∀ W₁ W₂ : (Fin n → ℝ) →L[ℝ] ℝ,
      HasFDerivAt V W₁ y₁ → HasFDerivAt V W₂ y₂ → W₁ = W₂ → y₁ = y₂)
    : (IsMaxOn (fun y => Finset.sum Finset.univ (fun i => y i * π i) - V y) O y_star ↔
      (∀ i, π i = V' ((Pi.single i (1 : ℝ)) : Fin n → ℝ))) ∧
      (∀ y ∈ O, IsMaxOn (fun y => Finset.sum Finset.univ (fun i => y i * π i) - V y) O y →
        y = y_star) := by
  sorry

end DiscreteChoice
end StochFictPlay
