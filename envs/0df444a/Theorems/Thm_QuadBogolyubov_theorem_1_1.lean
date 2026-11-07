-- Prove2me | Theorems.Thm_QuadBogolyubov_theorem_1_1
-- name    : QuadBogolyubov.theorem_1_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:03:16.766955+00:00
-- url     : https://prove2.me/theorems/70fd4006-ceda-4297-9856-5576152fe247
-- title:
--   Theorem 1.1 — quadratic Bogolyubov
-- statement:
--   There is an absolute constant $C>0$ such that the following holds for all $n$. If $A\subseteq\mathbb F_2^n$ has density at least $\alpha>0$, then $A+A+A$ contains a non-empty quadratic variety $W$ of complexity $d_1+d_2\le C\alpha^{-C}$ such that for every $w\in W$ there are $a_1,\dots,a_7\in A$ with $w=a_1+\dots+a_7$ and, for every quadratic polynomial $q:\mathbb F_2^n\to\mathbb F_2$,
--   $$q(w)=q(a_1)+q(a_2)+q(a_3)+q(a_4)+q(a_5)+q(a_6)+q(a_7).$$
--   This is the quadratic analogue of Bogolyubov's lemma: a structured set inside a low-order sumset, together with a seven-point local-correction identity that holds simultaneously for all quadratic polynomials.
--
--   Differences from the source:
--   - generalization: "A ⊆ F₂ⁿ has density α > 0" → 0 < α and α · 2ⁿ ≤ |A|; reason: this is the form of Theorem 4.1 (p.10); exact density is the case α = |A|/2ⁿ
--   - reading: complexity poly(1/α) → d₁ + d₂ ≤ Cα^{−C}, with C absolute and fixed before n, A, α; reason: p.68 reads complexity as ℓ + q "as in the statement of the main theorem"; this implies §3's d₁, d₂ ≤ d, and since α ≤ 1 every polynomial in 1/α is bounded this way
--   - reading: "λ₀ + λ₁q₁ + ⋯ + λ_{d₂}q_{d₂} is not a linear function for any (λ₀, …, λ_{d₂}) ≠ 0" (§3, p.9) → `QuadVariety.q_indep`: for every λ ≠ 0, Σλⱼqⱼ agrees on V with no polynomial of degree ≤ 1; reason: as printed the condition fails for λ = (1, 0, …, 0), so no variety would exist; the same sentence names the intent, "quadratic parts are linearly independent"
--   - encoding: qⱼ : V → F₂ quadratic functions on V → global quadratic polynomials on F₂ⁿ, used only on V; reason: p.68: each quadratic function on V extends to a quadratic polynomial on F₂ⁿ
--   - encoding: F₂ⁿ → Fin n → ZMod 2; reason: Lean convention; the same set
--   - encoding: quadratic polynomial q : F₂ⁿ → F₂ → `IsQuadraticPoly q`: evaluation of an `MvPolynomial` of total degree ≤ 2, constant and linear terms included; reason: the literal meaning of "polynomial of degree at most two"
-- source:
--   Castro-Silva, Golovnev, Gur, Wolf, A Quadratic Bogolyubov Theorem and Quantum Worst-Case to Average-Case Reductions, STOC 2027 submission (held manuscript, sha256 9d91dee3…), Theorem 1.1, p.2; proof pp.15–16

import Mathlib
import Definitions.Def_QuadBogolyubov_QuadVariety

set_option autoImplicit false

open scoped BigOperators Pointwise

namespace QuadBogolyubov

/-- **Theorem 1.1 (Quadratic Bogolyubov).** There is an absolute constant `C > 0` such that for
every `n`, every `A ⊆ 𝔽₂ⁿ` and every `α > 0` with `|A| ≥ α 2ⁿ`, the sumset `A + A + A` contains a
non-empty quadratic variety `W` of complexity `d₁ + d₂ ≤ C α^{-C}` such that every `w ∈ W` is a sum
`w = a₁ + ⋯ + a₇` of points `aᵢ ∈ A` with `q(w) = q(a₁) + ⋯ + q(a₇)` for every quadratic polynomial
`q : 𝔽₂ⁿ → 𝔽₂`.

Castro-Silva, Golovnev, Gur, Wolf, *A Quadratic Bogolyubov Theorem and Quantum Worst-Case to
Average-Case Reductions*, STOC 2027 submission (held manuscript, sha256 9d91dee3…), Theorem 1.1, p.2: "If A ⊆ F₂ⁿ has density α > 0, then A+A+A contains a non-empty quadratic
variety W of complexity poly(1/α) such that for every w ∈ W, there exist a1, . . . , a7 ∈ A
satisfying w = a1 + a2 + a3 + a4 + a5 + a6 + a7 and that for every quadratic polynomial
q : F₂ⁿ → F2, q(w) = q(a1) + q(a2) + q(a3) + q(a4) + q(a5) + q(a6) + q(a7)."

**Formalization Note.** `𝔽₂ⁿ` is `Fin n → ZMod 2`. "complexity poly(1/α)" is read as
`d₁ + d₂ ≤ C · α^{-C}` with `C` absolute, quantified before `n`, `A` and `α` (p.68 calls a variety
of `ℓ` linear and `q` quadratic equations "of complexity at most ℓ+q, as in the statement of the
main theorem"). "density α" is `|A| ≥ α 2ⁿ` (the form of Theorem 4.1, p.10). The seven points are
indexed by `Fin 7`. A quadratic polynomial is the evaluation of a polynomial of total degree at
most two (`IsQuadraticPoly`), constant and linear terms included. -/
theorem theorem_1_1 :
    ∃ C : ℝ, 0 < C ∧
      ∀ (n : ℕ) (A : Finset (Fin n → ZMod 2)) (α : ℝ), 0 < α → α * 2 ^ n ≤ (A.card : ℝ) →
        ∃ W : QuadVariety n,
          ((W.d1 + W.d2 : ℕ) : ℝ) ≤ C * α ^ (-C) ∧
          W.carrier.Nonempty ∧
          W.carrier ⊆ A + A + A ∧
          ∀ w ∈ W.carrier, ∃ a : Fin 7 → (Fin n → ZMod 2),
            (∀ i, a i ∈ A) ∧ w = ∑ i, a i ∧
            ∀ q : (Fin n → ZMod 2) → ZMod 2, IsQuadraticPoly q → q w = ∑ i, q (a i) := by sorry

end QuadBogolyubov
