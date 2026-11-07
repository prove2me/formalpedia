-- Prove2me | Theorems.Thm_QuadBogolyubov_theorem_4_2
-- name    : QuadBogolyubov.theorem_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:04:49.256275+00:00
-- url     : https://prove2.me/theorems/881d6b89-9e29-4108-a7e6-fd114e02a39c
-- title:
--   Theorem 4.2 — robust quadratic Bogolyubov
-- statement:
--   There is an absolute constant $C>0$ such that the following holds for all $n$. If $A\subseteq\mathbb F_2^n$ has density at least $\alpha>0$, then there is a non-empty quadratic variety $W\subseteq A+A+A$ of complexity $d_1+d_2\le C\alpha^{-C}$ such that for every $x_0\in W$,
--   $$\mathbb E_{x_1,x_2,x_3\in\mathbb F_2^n}\prod_{\omega\in\{0,1\}^3\setminus\{0\}}\mathbf 1_{A\cap W}(x_0+\omega_1x_1+\omega_2x_2+\omega_3x_3)\ge 2^{-C\alpha^{-C}}.$$
--   This counts punctured cubes with all seven points in $A\cap W$, and it implies Theorem 1.1 at once.
--
--   **Formalization Note** One constant $C$ serves both bounds, since both weaken as $C$ grows.
--
--   Differences from the source:
--   - reading: codimension poly(1/α) and 2^{−poly(1/α)} → d₁ + d₂ ≤ Cα^{−C} and 2^{−Cα^{−C}}, with one absolute C fixed before n, A, α; reason: p.68 reads complexity as ℓ + q; since α ≤ 1 every polynomial in 1/α is bounded this way
--   - reading: "there exists a quadratic variety W ⊆ A + A + A" → also `W.carrier.Nonempty`; reason: the proof of Theorem 1.1 (p.15) takes x₀ ∈ W from this theorem, and the proof (p.14) gives δ_W(A) ≥ α > 0; an empty W would make the display vacuous
--   - reading: "λ₀ + λ₁q₁ + ⋯ + λ_{d₂}q_{d₂} is not a linear function for any (λ₀, …, λ_{d₂}) ≠ 0" (§3, p.9) → `QuadVariety.q_indep`: for every λ ≠ 0, Σλⱼqⱼ agrees on V with no polynomial of degree ≤ 1; reason: as printed the condition fails for λ = (1, 0, …, 0), so no variety would exist; the same sentence names the intent, "quadratic parts are linearly independent"
--   - encoding: qⱼ : V → F₂ quadratic functions on V → global quadratic polynomials on F₂ⁿ, used only on V; reason: p.68: each quadratic function on V extends to a quadratic polynomial on F₂ⁿ
--   - encoding: F₂ⁿ → Fin n → ZMod 2; reason: Lean convention; the same set
-- source:
--   Castro-Silva, Golovnev, Gur, Wolf, A Quadratic Bogolyubov Theorem and Quantum Worst-Case to Average-Case Reductions, STOC 2027 submission (held manuscript, sha256 9d91dee3…), Theorem 4.2, p.11; proof pp.14–15

import Mathlib
import Definitions.Def_QuadBogolyubov_gowersU3

set_option autoImplicit false

open scoped BigOperators Pointwise

namespace QuadBogolyubov

/-- **Theorem 4.2 (Robust quadratic Bogolyubov).** There is an absolute constant `C > 0` such
that for every `A ⊆ 𝔽₂ⁿ` with `|A| ≥ α 2ⁿ`, `α > 0`, there is a non-empty quadratic variety
`W ⊆ A + A + A` with `d₁ + d₂ ≤ C α^{-C}` such that for every `x₀ ∈ W`,
`𝔼_{x₁,x₂,x₃ ∈ 𝔽₂ⁿ} ∏_{ω ∈ {0,1}³ \ {0}} 1_{A∩W}(x₀ + ω₁x₁ + ω₂x₂ + ω₃x₃) ≥ 2^{-C α^{-C}}`.

Castro-Silva, Golovnev, Gur, Wolf, *A Quadratic Bogolyubov Theorem and Quantum Worst-Case to
Average-Case Reductions*, STOC 2027 submission (held manuscript, sha256 9d91dee3…), Theorem 4.2, p.11: "If A ⊆ F₂ⁿ has density at least α > 0, then there exists a quadratic
variety W ⊆ A + A + A of codimension poly(1/α) such that the following holds: for every x0 ∈ W,
we have E_{x1,x2,x3∈F₂ⁿ} ∏_{ω∈{0,1}³\{0}} 1A∩W(x0 + ω1x1 + ω2x2 + ω3x3) ≥ 2^{−poly(1/α)}."

**Formalization Note.** "codimension poly(1/α)" is `d₁ + d₂ ≤ C α^{-C}` and `2^{-poly(1/α)}` is
`2^{-C α^{-C}}`, with one absolute `C` (both bounds weaken as `C` grows, so one constant serves
both). The conclusion includes `W ≠ ∅`: the proof of Theorem 1.1 (p.15) takes a point `x₀ ∈ W`
from this theorem, and the proof of Theorem 4.2 (p.14) gives `δ_W(A) ≥ α > 0`. The triple
`(x₁, x₂, x₃)` is `x : Fin 3 → 𝔽₂ⁿ`, averaged uniformly; `ω ∈ {0,1}³` is `Fin 3 → ZMod 2`. -/
theorem theorem_4_2 :
    ∃ C : ℝ, 0 < C ∧
      ∀ (n : ℕ) (A : Finset (Fin n → ZMod 2)) (α : ℝ), 0 < α → α * 2 ^ n ≤ (A.card : ℝ) →
        ∃ W : QuadVariety n,
          ((W.d1 + W.d2 : ℕ) : ℝ) ≤ C * α ^ (-C) ∧
          W.carrier.Nonempty ∧
          W.carrier ⊆ A + A + A ∧
          ∀ x₀ ∈ W.carrier,
            (2 : ℝ) ^ (-(C * α ^ (-C))) ≤
              𝔼 x : Fin 3 → (Fin n → ZMod 2),
                ∏ ω ∈ Finset.univ.filter (fun ω : Fin 3 → ZMod 2 => ω ≠ 0),
                  (ind (A ∩ W.carrier) (x₀ + ∑ i, ω i • x i) : ℝ) := by sorry

end QuadBogolyubov
