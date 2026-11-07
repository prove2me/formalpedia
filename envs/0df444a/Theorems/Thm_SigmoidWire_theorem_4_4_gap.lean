-- Prove2me | Theorems.Thm_SigmoidWire_theorem_4_4_gap
-- name    : SigmoidWire.theorem_4_4_gap
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:07:18.702297+00:00
-- url     : https://prove2.me/theorems/61b93a9f-650d-4a44-ae0a-43766192a08a
-- title:
--   Proof sketch of Theorem 4.4: the gap $\zeta_1-\zeta_0\ge\delta/\kappa$ at the output gate
-- statement:
--   Let $\sigma$ be non-decreasing and $\kappa$-Lipschitz with $\kappa>0$, and let $C$ be a $\sigma$-circuit computing $f:\{0,1\}^n\to\{0,1\}$ with separation $\delta\ge0$. Write $\Lambda(x)$ for the argument of $\sigma$ at the output gate, so that $C(x)=\sigma(\Lambda(x))$. Then there are reals $\zeta_0,\zeta_1$ with $\zeta_1-\zeta_0\ge\delta/\kappa$ such that for every $x\in\{0,1\}^n$,
--
--   $$
--   f(x)=1\iff\Lambda(x)\ge\zeta_1,\qquad f(x)=0\iff\Lambda(x)\le\zeta_0.
--   $$
--
--   For a depth-two circuit $\Lambda(x)=\sum_iw_i\sigma_i(x)+\ell(x)$, so the circuit's output is decided by this real-valued combination with a margin.
--
--   Differences from the source:
--   - generalization: a depth-two σ-circuit, with Σᵢ wᵢσᵢ(x) + ℓ(x) → every σ-circuit, with the output gate's argument; reason: the argument of σ at the output gate of a depth-two circuit is exactly this sum, and the depth is not used
--   - encoding: κ-Lipschitz, with δ/κ in the conclusion → 0 < κ; reason: δ/κ is undefined at κ = 0; in Lean x/0 = 0
--   - encoding: separation δ, implicitly non-negative → 0 ≤ δ; reason: for δ < 0 the conclusion fails (a true and a false input may then have the same output), and a separation is non-negative throughout the paper
-- source:
--   Li, Reichman, Williams, Wu, New Gate, Weight and Wire Complexity Bounds for Sigmoid Neural Networks, STOC 2027 submission (manuscript sha256 2d6ef7af…), proof sketch of Theorem 4.4, p.20

import Mathlib
import Definitions.Def_SigmoidWire_Circuit
import Definitions.Def_SigmoidWire_ComputesSep

namespace SigmoidWire

/-- **Proof sketch of Theorem 4.4, the gap `ζ₁ − ζ₀ ≥ δ/κ` at the output gate.**

J. Li, D. Reichman, R. Williams, T. Wu, *New Gate, Weight and Wire Complexity Bounds for Sigmoid
Neural Networks*, STOC 2027 submission (manuscript sha256 2d6ef7af…), proof sketch of Theorem 4.4,
p.20 (PDF p.22): "As σ is non-decreasing and κ-Lipschitz, there exists ζ₀, ζ₁ such that
ζ₁ − ζ₀ ≥ δ/κ, and f(x) = 1 (resp. f(x) = 0) iff Σ_i w_iσ_i(x) + ℓ(x) ≥ ζ₁ (resp.
Σ_i w_iσ_i(x) + ℓ(x) ≤ ζ₀)."

**Formalization Note.** `Σ_i w_iσ_i(x) + ℓ(x)` is the pre-activation of the output gate,
`C.outPre σ x`. The statement is made for every σ-circuit (any depth), every monotone
`κ`-Lipschitz `σ` with `κ > 0` (so that `δ/κ` is defined) and every separation `δ ≥ 0`. -/
theorem theorem_4_4_gap (σ : ℝ → ℝ) (κ : ℝ) (hmono : Monotone σ) (hκ : 0 < κ)
    (hlip : ∀ x y : ℝ, |σ x - σ y| ≤ κ * |x - y|)
    (n : ℕ) (C : Circuit n) (f : (Fin n → Bool) → Bool) (δ : ℝ) (hδ : 0 ≤ δ)
    (hC : ComputesSep σ C f δ) :
    ∃ ζ₀ ζ₁ : ℝ, δ / κ ≤ ζ₁ - ζ₀ ∧
      ∀ x : Fin n → Bool, (f x = true ↔ ζ₁ ≤ C.outPre σ x) ∧
        (f x = false ↔ C.outPre σ x ≤ ζ₀) := by sorry

end SigmoidWire
