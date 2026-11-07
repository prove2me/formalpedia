-- Prove2me | Theorems.Thm_QuadBogolyubov_theorem_4_6
-- name    : QuadBogolyubov.theorem_4_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:06:42.278256+00:00
-- url     : https://prove2.me/theorems/11ec5632-4d1a-40d1-b46c-141fd9bcfd6a
-- title:
--   Theorem 4.6 — quadratic uniformity via density increment
-- statement:
--   There are absolute constants $C_0,K\ge1$ such that for every $C\ge C_0$, every $\varepsilon>0$ and every $A\subseteq\mathbb F_2^n$ there is a quadratic variety $W$ of complexity $(d_1,d_2)$ with
--   $$d_1+d_2\le C\cdot K\varepsilon^{-K},\qquad \mathrm{rk}(W)\ge C\big(d_2+\log_2(1/\varepsilon)\big),$$
--   such that $\delta_W(A)\ge|A|/2^n$ and $\beta_W(A)\le\varepsilon$.
--
--   So every set has at least its ambient density on some high-rank variety of bounded complexity, and it is quadratically uniform there.
--
--   Differences from the source:
--   - reading: "let C0 be the constant from Theorem 4.3" → an existential threshold C₀ ≥ 1 inside this item; reason: items do not share constants; the C₀ of Theorem 4.3 is itself only existential, and that theorem remains true when C₀ is enlarged
--   - reading: C poly(1/ε) → C · K ε^{−K}, with K ≥ 1 absolute, chosen before C and ε; reason: the polynomial does not depend on C: the proof has d₁ ≤ Cs³ + Cs² log(1/ε) with s ≤ 4/γ = 4ε^{−k₀}, and ε > 1/2 reduces to ε = 1/2 once K is large
--   - reading: log → log₂ (`Real.logb 2`); reason: Appendix D writes log₂; the base only moves the constant
--   - encoding: rk(W) as a number, the minimum over λ ≠ 0 → `HasRankAtLeast W r` for a real lower bound r, vacuous when d₂ = 0; reason: p.68: "When q = 0, we say by convention that the rank is infinite"; a minimum over the empty set has no number in ℝ or ℕ
--   - reading: "λ₀ + λ₁q₁ + ⋯ + λ_{d₂}q_{d₂} is not a linear function for any (λ₀, …, λ_{d₂}) ≠ 0" (§3, p.9) → `QuadVariety.q_indep`: for every λ ≠ 0, Σλⱼqⱼ agrees on V with no polynomial of degree ≤ 1; reason: as printed the condition fails for λ = (1, 0, …, 0), so no variety would exist; the same sentence names the intent, "quadratic parts are linearly independent"
--   - encoding: qⱼ : V → F₂ quadratic functions on V → global quadratic polynomials on F₂ⁿ, used only on V; reason: p.68: each quadratic function on V extends to a quadratic polynomial on F₂ⁿ
--   - encoding: δ_W(A) = |A ∩ W|/|W|, β_W(A) → `relDensity`, `quadBias`, with Lean value 0 at empty W; reason: an empty W can meet δ_W(A) ≥ |A|/2ⁿ only when A = ∅, where the theorem is trivial anyway
--   - encoding: F₂ⁿ → Fin n → ZMod 2; reason: Lean convention; the same set
-- source:
--   Castro-Silva, Golovnev, Gur, Wolf, A Quadratic Bogolyubov Theorem and Quantum Worst-Case to Average-Case Reductions, STOC 2027 submission (held manuscript, sha256 9d91dee3…), Theorem 4.6, p.12; proof p.14

import Mathlib
import Definitions.Def_QuadBogolyubov_HasRankAtLeast
import Definitions.Def_QuadBogolyubov_quadBias

set_option autoImplicit false

open scoped BigOperators Pointwise

namespace QuadBogolyubov

/-- **Theorem 4.6 (Quadratic uniformity via density increment).** There are constants
`C₀, K ≥ 1` such that for every `C ≥ C₀`, every `ε > 0` and every `A ⊆ 𝔽₂ⁿ` there is a quadratic
variety `W` of complexity `(d₁, d₂)` with `d₁ + d₂ ≤ C · K ε^{-K}` and
`rk(W) ≥ C (d₂ + log₂(1/ε))`, such that `δ_W(A) ≥ |A|/2ⁿ` and `β_W(A) ≤ ε`.

Castro-Silva, Golovnev, Gur, Wolf, *A Quadratic Bogolyubov Theorem and Quantum Worst-Case to
Average-Case Reductions*, STOC 2027 submission (held manuscript, sha256 9d91dee3…), Theorem 4.6, p.12: "Let ε > 0 and let C0 be the constant from Theorem 4.3. Then, for any
C ≥ C0 and any set A ⊆ F₂ⁿ, there exists a quadratic variety W ⊆ F₂ⁿ of complexity (d1, d2) with
d1 + d2 ≤ C poly(1/ε) and rk(W) ≥ C(d2 + log(1/ε)) such that δW(A) ≥ |A|/2ⁿ and βW(A) ≤ ε."

**Formalization Note.** Items do not share constants, so "the constant from Theorem 4.3" is an
existential threshold `C₀ ≥ 1` (Theorem 4.3 stays true when its `C₀` is enlarged, so the paper's
statement is that some threshold works). "C poly(1/ε)" is `C · K ε^{-K}` with `K ≥ 1` absolute,
chosen before `C` and `ε`. `log` is `log₂`. `rk(W) ≥ r` is `HasRankAtLeast W r` (vacuous, i.e.
infinite rank, when `d₂ = 0`). `δ_W(A)` is `relDensity W A` and `β_W(A)` is `quadBias W A`. -/
theorem theorem_4_6 :
    ∃ C₀ : ℝ, 1 ≤ C₀ ∧ ∃ K : ℝ, 1 ≤ K ∧
      ∀ C : ℝ, C₀ ≤ C → ∀ ε : ℝ, 0 < ε →
        ∀ (n : ℕ) (A : Finset (Fin n → ZMod 2)),
          ∃ W : QuadVariety n,
            ((W.d1 + W.d2 : ℕ) : ℝ) ≤ C * (K * ε ^ (-K)) ∧
            HasRankAtLeast W (C * ((W.d2 : ℝ) + Real.logb 2 (1 / ε))) ∧
            (A.card : ℝ) / 2 ^ n ≤ relDensity W A ∧
            quadBias W A ≤ ε := by sorry

end QuadBogolyubov
