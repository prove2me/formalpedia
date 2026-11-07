-- Prove2me | Theorems.Thm_QuadBogolyubov_lemma_D_8
-- name    : QuadBogolyubov.lemma_D_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:08:47.330589+00:00
-- url     : https://prove2.me/theorems/db8bacd1-54ab-421c-bb22-b82f822b4971
-- title:
--   Lemma D.8 — number of Gowers cubes in $W$
-- statement:
--   There are absolute constants $C,K>0$ such that for every $0<\eta\le1$ and every quadratic variety $W$ as in (28) of rank $\mathrm{rk}(W)\ge C(d+\log_2(\eta^{-1}))$,
--   $$\big||\Omega(W)|-2^{4n-7d}\big|\le K\eta\,2^{4n-7d}\quad\text{and}\quad\big|\|\mathbf 1_W\|_{U^3}^8-2^{-7d}\big|\le K\eta\,2^{-7d}.$$
--   So $W$ contains the expected number of Gowers cubes: the eight corner conditions amount to $7d$ constraints.
--
--   **Formalization Note** $\|\mathbf 1_W\|_{U^3}^8$ is the real part of the cube average of Definition 3.3.
--
--   Differences from the source:
--   - reading: rk(W) ≥ C(d + log₂(η⁻¹)) with C unspecified; (1 + O(η))X; + O(η) → ∃ absolute C, K > 0 fixed before η, n, W and the functions; |· − X| ≤ KηX; + Kη; reason: the usual meaning of the O-notation and of the constant C in Appendix D
--   - encoding: "as in (28)": complexity (0, d), containing 0, written W = {q = 0} with qⱼ(0) = 0 → `IsRooted W`: d₁ = 0, every bⱼ = 0, every qⱼ(0) = 0, with d = W.d2; reason: the normalization (28) itself, written as hypotheses
--   - encoding: rk(W) as a number, the minimum over λ ≠ 0 → `HasRankAtLeast W r` for a real lower bound r, vacuous when d₂ = 0; reason: p.68: "When q = 0, we say by convention that the rank is infinite"; a minimum over the empty set has no number in ℝ or ℕ
--   - reading: "λ₀ + λ₁q₁ + ⋯ + λ_{d₂}q_{d₂} is not a linear function for any (λ₀, …, λ_{d₂}) ≠ 0" (§3, p.9) → `QuadVariety.q_indep`: for every λ ≠ 0, Σλⱼqⱼ agrees on V with no polynomial of degree ≤ 1; reason: as printed the condition fails for λ = (1, 0, …, 0), so no variety would exist; the same sentence names the intent, "quadratic parts are linearly independent"
--   - encoding: qⱼ : V → F₂ quadratic functions on V → global quadratic polynomials on F₂ⁿ, used only on V; reason: p.68: each quadratic function on V extends to a quadratic polynomial on F₂ⁿ
--   - reading: "or equivalently" → both clauses are stated as a conjunction; reason: each clause of the printed statement is a conclusion; they are equal up to the factor |G|⁴
--   - encoding: F₂ⁿ → Fin n → ZMod 2; reason: Lean convention; the same set
-- source:
--   Castro-Silva, Golovnev, Gur, Wolf, A Quadratic Bogolyubov Theorem and Quantum Worst-Case to Average-Case Reductions, STOC 2027 submission (held manuscript, sha256 9d91dee3…), Lemma D.8, p.55

import Mathlib
import Definitions.Def_QuadBogolyubov_IsRooted
import Definitions.Def_QuadBogolyubov_cubeSet
import Definitions.Def_QuadBogolyubov_gowersU3

set_option autoImplicit false

open scoped BigOperators Pointwise

namespace QuadBogolyubov

/-- **Lemma D.8 (Number of Gowers cubes in `W`).** There are absolute constants `C, K > 0` such
that for every `0 < η ≤ 1` and every quadratic variety `W` as in (28) with
`rk(W) ≥ C(d + log₂(η⁻¹))`, `| |Ω(W)| − 2^{4n−7d} | ≤ Kη · 2^{4n−7d}` and
`| ‖1_W‖⁸_{U³} − 2^{−7d} | ≤ Kη · 2^{−7d}`.

Castro-Silva, Golovnev, Gur, Wolf, *A Quadratic Bogolyubov Theorem and Quantum Worst-Case to
Average-Case Reductions*, STOC 2027 submission (held manuscript, sha256 9d91dee3…), Lemma D.8, p.55: "Let 0 < η ≤ 1, and let W be a quadratic variety as in (28) of rank
rk(W) ≥ C(d + log2(η⁻¹)). Then |Ω(W)| = (1 + O(η))2^{4n−7d}, or equivalently,
∥1W∥⁸_{U3} = (1 + O(η))2^{−7d}."

**Formalization Note.** "as in (28)" is `IsRooted W` (complexity `(0, d)`, `qⱼ(0) = 0`, `bⱼ = 0`)
with `d = W.d2`. `C` is the sufficiently large constant of Appendix D and `X = (1 + O(η))Y` is
`|X − Y| ≤ K η Y`, with `C, K` absolute and fixed first. `‖1_W‖⁸_{U³}` is the real part of the
cube average of Definition 3.3 (`gowersU3Pow8`), and `Ω(W)` is `cubeSet W`. Both clauses are
stated. -/
theorem lemma_D_8 :
    ∃ C K : ℝ, 0 < C ∧ 0 < K ∧
      ∀ η : ℝ, 0 < η → η ≤ 1 → ∀ (n : ℕ) (W : QuadVariety n), IsRooted W →
        HasRankAtLeast W (C * ((W.d2 : ℝ) + Real.logb 2 η⁻¹)) →
        |((cubeSet W).card : ℝ) - (2 : ℝ) ^ (4 * (n : ℝ) - 7 * (W.d2 : ℝ))| ≤
            K * η * (2 : ℝ) ^ (4 * (n : ℝ) - 7 * (W.d2 : ℝ)) ∧
          |(gowersU3Pow8 (fun x => (ind W.carrier x : ℂ))).re - (2 : ℝ) ^ (-(7 * (W.d2 : ℝ)))| ≤
            K * η * (2 : ℝ) ^ (-(7 * (W.d2 : ℝ))) := by sorry

end QuadBogolyubov
