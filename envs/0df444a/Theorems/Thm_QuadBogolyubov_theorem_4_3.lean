-- Prove2me | Theorems.Thm_QuadBogolyubov_theorem_4_3
-- name    : QuadBogolyubov.theorem_4_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:04:34.8912+00:00
-- url     : https://prove2.me/theorems/f0e03224-14a7-420e-b078-5692bb4c382a
-- title:
--   Theorem 4.3 — relative $U^3$ inverse theorem
-- statement:
--   There are constants $C_0,k_0\ge1$ such that for every $\varepsilon\in(0,1/2]$ and every quadratic variety $W$ of complexity $(d_1,d_2)$ with $\mathrm{rk}(W)\ge C_0(d_2+\log_2(1/\varepsilon))$, every $f:W\to[-1,1]$ with $\|f\|_{U^3(W)}\ge\varepsilon$ correlates with a quadratic phase: there is a quadratic function $q$ with
--   $$\Big|\mathbb E_{x\in W}f(x)(-1)^{q(x)}\Big|\ge\varepsilon^{k_0}.$$
--   This passes from a large relative $U^3$ norm to correlation with a quadratic phase on the ambient affine subspace of $W$. The paper calls it a slight rephrasing of Prendiville's result and outlines the characteristic-2 changes in its Appendix E.
--
--   **Formalization Note** $k_0$ is real, which is equivalent to an integer exponent because $\varepsilon<1$.
--
--   Differences from the source:
--   - encoding: bounded f : W → [−1, 1] → f : 𝔽₂ⁿ → ℝ with |f x| ≤ 1 for x ∈ W; reason: values off W do not enter either the local norm or the expectation over W
--   - encoding: q : V → F₂ quadratic → a global `IsQuadraticPoly q`; reason: p.68: every quadratic function on V extends to F₂ⁿ, and the restriction of a global one is a quadratic function on V
--   - encoding: W non-empty (Definition 3.4 and E over W) → no separate hypothesis; reason: ε ≤ ‖f‖_{U³(W)} with ε > 0 forces W ≠ ∅, because the Lean local norm is 0 on empty W
--   - reading: log → log₂ (`Real.logb 2`); reason: Appendix D writes log₂; the base only moves the constant
--   - encoding: rk(W) as a number, the minimum over λ ≠ 0 → `HasRankAtLeast W r` for a real lower bound r, vacuous when d₂ = 0; reason: p.68: "When q = 0, we say by convention that the rank is infinite"; a minimum over the empty set has no number in ℝ or ℕ
--   - reading: "λ₀ + λ₁q₁ + ⋯ + λ_{d₂}q_{d₂} is not a linear function for any (λ₀, …, λ_{d₂}) ≠ 0" (§3, p.9) → `QuadVariety.q_indep`: for every λ ≠ 0, Σλⱼqⱼ agrees on V with no polynomial of degree ≤ 1; reason: as printed the condition fails for λ = (1, 0, …, 0), so no variety would exist; the same sentence names the intent, "quadratic parts are linearly independent"
--   - encoding: qⱼ : V → F₂ quadratic functions on V → global quadratic polynomials on F₂ⁿ, used only on V; reason: p.68: each quadratic function on V extends to a quadratic polynomial on F₂ⁿ
--   - encoding: F₂ⁿ → Fin n → ZMod 2; reason: Lean convention; the same set
--   - encoding: (−1)^{q(x)} with exponent in F₂ → `(-1 : ℝ) ^ (q x).val`; reason: the exponent is the value in {0, 1}; casting to ℝ would break 1 + 1 = 0
-- source:
--   Castro-Silva, Golovnev, Gur, Wolf, A Quadratic Bogolyubov Theorem and Quantum Worst-Case to Average-Case Reductions, STOC 2027 submission (held manuscript, sha256 9d91dee3…), Theorem 4.3, p.11; App. E, pp.65–67

import Mathlib
import Definitions.Def_QuadBogolyubov_HasRankAtLeast
import Definitions.Def_QuadBogolyubov_gowersU3

set_option autoImplicit false

open scoped BigOperators Pointwise

namespace QuadBogolyubov

/-- **Theorem 4.3 (Relative `U³` inverse theorem).** There are constants `C₀, k₀ ≥ 1` such that
for every `ε ∈ (0, 1/2]` and every quadratic variety `W` of complexity `(d₁, d₂)` with
`rk(W) ≥ C₀ (d₂ + log₂(1/ε))`, every `f : W → [-1, 1]` with `‖f‖_{U³(W)} ≥ ε` correlates with a
quadratic phase: there is a quadratic `q` with `|𝔼_{x∈W} f(x)(-1)^{q(x)}| ≥ ε^{k₀}`.

Castro-Silva, Golovnev, Gur, Wolf, *A Quadratic Bogolyubov Theorem and Quantum Worst-Case to
Average-Case Reductions*, STOC 2027 submission (held manuscript, sha256 9d91dee3…), Theorem 4.3, p.11: "There exist constants C0, k0 ≥ 1 such that the following holds for all
ε ∈ (0, 1/2] and d1, d2 ∈ N. Suppose W is a quadratic variety of complexity (d1, d2) and rank
rk(W) ≥ C0(d2 + log(1/ε)). Then, for every bounded function f : W → [−1, 1] satisfying
∥f∥U3(W) ≥ ε, there exists a quadratic function q : V → F2 such that
|E_{x∈W} f(x)(−1)^{q(x)}| ≥ ε^{k0}."

**Formalization Note.** `f` is a real function on `𝔽₂ⁿ` bounded by `1` on `W`; its values off `W`
do not enter. The quadratic function `q : V → 𝔽₂` on the ambient affine subspace is a global
quadratic polynomial (every quadratic function on `V` extends to one, p.68). `(-1)^{q(x)}` is
`(-1)^{(q x).val}`. `log` is `log₂`; `k₀` is real (equivalent, since `ε < 1`). For empty `W` the
Lean local norm is `0`, so the hypothesis `‖f‖_{U³(W)} ≥ ε > 0` forces `W ≠ ∅`, as Def. 3.4
requires. -/
theorem theorem_4_3 :
    ∃ C₀ k₀ : ℝ, 1 ≤ C₀ ∧ 1 ≤ k₀ ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 →
        ∀ (n : ℕ) (W : QuadVariety n),
          HasRankAtLeast W (C₀ * ((W.d2 : ℝ) + Real.logb 2 (1 / ε))) →
          ∀ f : (Fin n → ZMod 2) → ℝ, (∀ x ∈ W.carrier, |f x| ≤ 1) →
            ε ≤ localU3 W (fun x => (f x : ℂ)) →
            ∃ q : (Fin n → ZMod 2) → ZMod 2, IsQuadraticPoly q ∧
              ε ^ k₀ ≤ |𝔼 x ∈ W.carrier, f x * (-1 : ℝ) ^ (q x).val| := by sorry

end QuadBogolyubov
