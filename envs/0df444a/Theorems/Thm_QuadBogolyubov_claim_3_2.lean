-- Prove2me | Theorems.Thm_QuadBogolyubov_claim_3_2
-- name    : QuadBogolyubov.claim_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:05:10.963268+00:00
-- url     : https://prove2.me/theorems/c9120542-8349-4b56-ae31-746f821eff21
-- title:
--   Claim 3.2 — translates of quadratic varieties
-- statement:
--   For every quadratic variety $W\subseteq\mathbb F_2^n$ and every $x_0\in\mathbb F_2^n$, the translate $x_0+W$ is a quadratic variety with the same complexity $(d_1,d_2)$ and the same rank as $W$.
--
--   Translation is what lets the counting lemma work with varieties containing $0$.
--
--   Differences from the source:
--   - reading: "the same codimension and the same rank" → ∃ W′ with carrier x₀ + W, the same d₁, d₂, and ∀ r, rk(W′) ≥ r ↔ rk(W) ≥ r; reason: codimension means the complexity (d₁, d₂) of the representation; two ranks are equal exactly when they have the same lower bounds, which also covers d₂ = 0
--   - reading: "λ₀ + λ₁q₁ + ⋯ + λ_{d₂}q_{d₂} is not a linear function for any (λ₀, …, λ_{d₂}) ≠ 0" (§3, p.9) → `QuadVariety.q_indep`: for every λ ≠ 0, Σλⱼqⱼ agrees on V with no polynomial of degree ≤ 1; reason: as printed the condition fails for λ = (1, 0, …, 0), so no variety would exist; the same sentence names the intent, "quadratic parts are linearly independent"
--   - encoding: qⱼ : V → F₂ quadratic functions on V → global quadratic polynomials on F₂ⁿ, used only on V; reason: p.68: each quadratic function on V extends to a quadratic polynomial on F₂ⁿ
--   - encoding: F₂ⁿ → Fin n → ZMod 2; reason: Lean convention; the same set
-- source:
--   Castro-Silva, Golovnev, Gur, Wolf, A Quadratic Bogolyubov Theorem and Quantum Worst-Case to Average-Case Reductions, STOC 2027 submission (held manuscript, sha256 9d91dee3…), Claim 3.2, p.10

import Mathlib
import Definitions.Def_QuadBogolyubov_HasRankAtLeast

set_option autoImplicit false

open scoped BigOperators Pointwise

namespace QuadBogolyubov

/-- **Claim 3.2 (Translates).** For every quadratic variety `W ⊆ 𝔽₂ⁿ` and every `x₀ ∈ 𝔽₂ⁿ`, the
translate `x₀ + W` is a quadratic variety with the same complexity `(d₁, d₂)` and the same rank.

Castro-Silva, Golovnev, Gur, Wolf, *A Quadratic Bogolyubov Theorem and Quantum Worst-Case to
Average-Case Reductions*, STOC 2027 submission (held manuscript, sha256 9d91dee3…), Claim 3.2, p.10: "If W ⊆ F₂ⁿ is a quadratic variety, then for all x0 ∈ F₂ⁿ the set x0 + W is
a quadratic variety with the same codimension and the same rank as W."

**Formalization Note.** "codimension" is the complexity `(d₁, d₂)` of the representation. "the same
rank" is `∀ r, rk(W') ≥ r ↔ rk(W) ≥ r` (`HasRankAtLeast`), which also covers `d₂ = 0` (infinite
rank). `x₀ + W` is the pointwise translate `x₀ +ᵥ W.carrier`. -/
theorem claim_3_2 {n : ℕ} (W : QuadVariety n) (x₀ : Fin n → ZMod 2) :
    ∃ W' : QuadVariety n, W'.carrier = x₀ +ᵥ W.carrier ∧ W'.d1 = W.d1 ∧ W'.d2 = W.d2 ∧
      ∀ r : ℝ, HasRankAtLeast W' r ↔ HasRankAtLeast W r := by sorry

end QuadBogolyubov
