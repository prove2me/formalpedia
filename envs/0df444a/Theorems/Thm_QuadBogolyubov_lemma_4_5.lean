-- Prove2me | Theorems.Thm_QuadBogolyubov_lemma_4_5
-- name    : QuadBogolyubov.lemma_4_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:07:38.610718+00:00
-- url     : https://prove2.me/theorems/ca3b182e-dc9e-4026-a4c3-e492155a6946
-- title:
--   Lemma 4.5 — counting punctured 3-cubes in quadratic varieties
-- statement:
--   Let $W\subseteq\mathbb F_2^n$ be a quadratic variety of complexity $(d_1,d_2)$ and let $x_0\in\mathbb F_2^n$. If $x_0\in W$, then
--   $$\big|\Lambda(\mathbf 1_{x_0+W})-2^{-3d_1-6d_2}\big|\le2^{-3d_1-\mathrm{rk}(W)/2},$$
--   and otherwise $\Lambda(\mathbf 1_{x_0+W})=0$.
--
--   This gives the main term of the count of punctured cubes in a variety.
--
--   **Formalization Note** For $d_2=0$ the first clause holds for every real $r$ in place of $\mathrm{rk}(W)$, which forces $\Lambda(\mathbf 1_{x_0+W})=2^{-3d_1}$.
--
--   Differences from the source:
--   - encoding: 2^{−3d₁−rk(W)/2} → for every r with `HasRankAtLeast W r`, the bound 2^{−3d₁−r/2}; reason: the bound decreases in r, so this is the bound at r = rk(W), and at d₂ = 0 it matches rk = ∞ (p.68)
--   - reading: "λ₀ + λ₁q₁ + ⋯ + λ_{d₂}q_{d₂} is not a linear function for any (λ₀, …, λ_{d₂}) ≠ 0" (§3, p.9) → `QuadVariety.q_indep`: for every λ ≠ 0, Σλⱼqⱼ agrees on V with no polynomial of degree ≤ 1; reason: as printed the condition fails for λ = (1, 0, …, 0), so no variety would exist; the same sentence names the intent, "quadratic parts are linearly independent"
--   - encoding: qⱼ : V → F₂ quadratic functions on V → global quadratic polynomials on F₂ⁿ, used only on V; reason: p.68: each quadratic function on V extends to a quadratic polynomial on F₂ⁿ
--   - encoding: x₀ + W → `x₀ +ᵥ W.carrier`; reason: pointwise translate
--   - encoding: F₂ⁿ → Fin n → ZMod 2; reason: Lean convention; the same set
-- source:
--   Castro-Silva, Golovnev, Gur, Wolf, A Quadratic Bogolyubov Theorem and Quantum Worst-Case to Average-Case Reductions, STOC 2027 submission (held manuscript, sha256 9d91dee3…), Lemma 4.5, p.11; proof App. D.1, pp.56–57

import Mathlib
import Definitions.Def_QuadBogolyubov_HasRankAtLeast
import Definitions.Def_QuadBogolyubov_gowersU3
import Definitions.Def_QuadBogolyubov_Lam

set_option autoImplicit false

open scoped BigOperators Pointwise

namespace QuadBogolyubov

/-- **Lemma 4.5 (Counting punctured 3-cubes in quadratic varieties).** Let `W ⊆ 𝔽₂ⁿ` be a
quadratic variety of complexity `(d₁, d₂)` and `x₀ ∈ 𝔽₂ⁿ`. If `x₀ ∈ W`, then
`|Λ(1_{x₀+W}) − 2^{−3d₁−6d₂}| ≤ 2^{−3d₁−rk(W)/2}`; otherwise `Λ(1_{x₀+W}) = 0`.

Castro-Silva, Golovnev, Gur, Wolf, *A Quadratic Bogolyubov Theorem and Quantum Worst-Case to
Average-Case Reductions*, STOC 2027 submission (held manuscript, sha256 9d91dee3…), Lemma 4.5, p.11: "Let W ⊆ F₂ⁿ be a quadratic variety of complexity (d1, d2). Then for all
x0 ∈ F₂ⁿ, |Λ(1x0+W) − 2^{−3d1−6d2}| ≤ 2^{−3d1−rk(W)/2} if x0 ∈ W, and Λ(1x0+W) = 0 otherwise."

**Formalization Note.** The rank enters through every lower bound `r` with `HasRankAtLeast W r`
(the bound decreases in `r`, so this is the bound at `r = rk(W)`); for `d₂ = 0` (infinite rank)
it forces `Λ(1_{x₀+W}) = 2^{−3d₁}`. `x₀ + W` is the pointwise translate `x₀ +ᵥ W.carrier`, and
`Λ(f) = Λ(f, …, f)`. -/
theorem lemma_4_5 {n : ℕ} (W : QuadVariety n) (x₀ : Fin n → ZMod 2) :
    (x₀ ∈ W.carrier → ∀ r : ℝ, HasRankAtLeast W r →
      |Lam (fun _ => ind (x₀ +ᵥ W.carrier)) - (2 : ℝ) ^ (-(3 * (W.d1 : ℝ)) - 6 * (W.d2 : ℝ))| ≤
        (2 : ℝ) ^ (-(3 * (W.d1 : ℝ)) - r / 2)) ∧
    (x₀ ∉ W.carrier → Lam (fun _ => ind (x₀ +ᵥ W.carrier)) = 0) := by sorry

end QuadBogolyubov
