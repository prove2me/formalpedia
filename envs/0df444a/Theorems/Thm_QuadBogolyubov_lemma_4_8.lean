-- Prove2me | Theorems.Thm_QuadBogolyubov_lemma_4_8
-- name    : QuadBogolyubov.lemma_4_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:06:52.829833+00:00
-- url     : https://prove2.me/theorems/65f798af-6d77-4a6d-90a5-d08a6d3d14d2
-- title:
--   Lemma 4.8 — regularisation step
-- statement:
--   Let $W$ be a quadratic variety of complexity $(d_1,d_2)$ and let $C,K\ge0$. For every $A\subseteq\mathbb F_2^n$ there is a quadratic variety $W'$ of complexity $(d_1',d_2')$ with:
--
--   1. $d_2'\le d_2$ and $d_1'\le d_1+C(d_2-d_2')(d_2+K)$;
--   2. $\mathrm{rk}(W')\ge C(d_2+K)$;
--   3. $\delta_{W'}(A)\ge\delta_W(A)$.
--
--   So a variety can be made high-rank at a controlled cost in linear equations, without losing the density of a given set.
--
--   **Formalization Note** The first inequality of (1) is stated in $\mathbb N$ and the second in $\mathbb R$. The statement does not require $W'\subseteq W$, as printed; the proof's $W'$ does satisfy it.
--
--   Differences from the source:
--   - encoding: rk(W) as a number, the minimum over λ ≠ 0 → `HasRankAtLeast W r` for a real lower bound r, vacuous when d₂ = 0; reason: p.68: "When q = 0, we say by convention that the rank is infinite"; a minimum over the empty set has no number in ℝ or ℕ
--   - reading: "λ₀ + λ₁q₁ + ⋯ + λ_{d₂}q_{d₂} is not a linear function for any (λ₀, …, λ_{d₂}) ≠ 0" (§3, p.9) → `QuadVariety.q_indep`: for every λ ≠ 0, Σλⱼqⱼ agrees on V with no polynomial of degree ≤ 1; reason: as printed the condition fails for λ = (1, 0, …, 0), so no variety would exist; the same sentence names the intent, "quadratic parts are linearly independent"
--   - encoding: qⱼ : V → F₂ quadratic functions on V → global quadratic polynomials on F₂ⁿ, used only on V; reason: p.68: each quadratic function on V extends to a quadratic polynomial on F₂ⁿ
--   - encoding: δ_W(A) for a possibly empty W → `relDensity` with Lean value 0 at empty W; reason: the paper leaves |A ∩ W|/|W| undefined at empty W; (iii) can be met by an empty W′ only when δ_W(A) = 0, where it says nothing
--   - encoding: F₂ⁿ → Fin n → ZMod 2; reason: Lean convention; the same set
-- source:
--   Castro-Silva, Golovnev, Gur, Wolf, A Quadratic Bogolyubov Theorem and Quantum Worst-Case to Average-Case Reductions, STOC 2027 submission (held manuscript, sha256 9d91dee3…), Lemma 4.8, p.13

import Mathlib
import Definitions.Def_QuadBogolyubov_HasRankAtLeast
import Definitions.Def_QuadBogolyubov_quadBias

set_option autoImplicit false

open scoped BigOperators Pointwise

namespace QuadBogolyubov

/-- **Lemma 4.8 (Regularisation step).** Let `W` be a quadratic variety of complexity `(d₁, d₂)`
and `C, K ≥ 0`. For every `A ⊆ 𝔽₂ⁿ` there is a quadratic variety `W'` of complexity `(d₁', d₂')`
with (i) `d₂' ≤ d₂` and `d₁' ≤ d₁ + C(d₂ − d₂')(d₂ + K)`; (ii) `rk(W') ≥ C(d₂ + K)`;
(iii) `δ_{W'}(A) ≥ δ_W(A)`.

Castro-Silva, Golovnev, Gur, Wolf, *A Quadratic Bogolyubov Theorem and Quantum Worst-Case to
Average-Case Reductions*, STOC 2027 submission (held manuscript, sha256 9d91dee3…), Lemma 4.8, p.13: "Let W ⊆ F₂ⁿ be a quadratic variety of complexity (d1, d2), and let
C, K ≥ 0. Then, for any set A ⊆ F₂ⁿ, there exists a quadratic variety W′ of complexity (d′1, d′2)
with the following properties: (i) d′2 ≤ d2 and d′1 ≤ d1 + C(d2 − d′2)(d2 + K);
(ii) rk(W′) ≥ C(d2 + K); (iii) δW′(A) ≥ δW(A)."

**Formalization Note.** (i) is stated in `ℝ`; `d₂ − d₂' ≥ 0` by the first half. (ii) is
`HasRankAtLeast W' (C (d₂ + K))` with the `d₂` of `W` (infinite rank when `d₂' = 0`). The statement
does not require `W' ⊆ W` (the proof's `W'` satisfies it). For empty `W` the Lean `δ_W(A)` is `0`. -/
theorem lemma_4_8 {n : ℕ} (W : QuadVariety n) (C K : ℝ) (hC : 0 ≤ C) (hK : 0 ≤ K)
    (A : Finset (Fin n → ZMod 2)) :
    ∃ W' : QuadVariety n,
      (W'.d2 ≤ W.d2 ∧
        (W'.d1 : ℝ) ≤ (W.d1 : ℝ) + C * ((W.d2 : ℝ) - (W'.d2 : ℝ)) * ((W.d2 : ℝ) + K)) ∧
      HasRankAtLeast W' (C * ((W.d2 : ℝ) + K)) ∧
      relDensity W A ≤ relDensity W' A := by sorry

end QuadBogolyubov
