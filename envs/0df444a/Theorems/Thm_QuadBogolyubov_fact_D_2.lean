-- Prove2me | Theorems.Thm_QuadBogolyubov_fact_D_2
-- name    : QuadBogolyubov.fact_D_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:08:36.688552+00:00
-- url     : https://prove2.me/theorems/dfbd860c-0f21-402c-8026-dfa86b2e1b8f
-- title:
--   Fact D.2 — quadratic exponential sums of high rank are small
-- statement:
--   Let $q:G\to\mathbb F_2$ be quadratic, let $\ell:G\to\mathbb F_2$ be linear, with $G=\mathbb F_2^n$, and suppose that $\beta_q$ has rank $r$. Then
--   $$\Big|\mathbb E_{x\in G}(-1)^{q(x)+\ell(x)}\Big|\le2^{-r/2}.$$
--   This is the basic estimate behind all size and counting bounds of Appendix D.
--
--   Differences from the source:
--   - encoding: β_q has rank r → `bilinRank (bilin q) = r`, the dimension of the span of the functionals β_q(h, ·); reason: p.52: rk(β_q) is the rank of h ↦ β_q(h, ·)
--   - encoding: (−1)^{q(x)+ℓ(x)} with exponent in F₂ → `(-1 : ℝ) ^ (q x + ℓ x).val`; reason: the exponent is the value in {0, 1}; casting to ℝ would break 1 + 1 = 0
--   - encoding: F₂ⁿ → Fin n → ZMod 2; reason: Lean convention; the same set
--   - encoding: q : G → F₂ quadratic → `IsQuadraticPoly q`: evaluation of an `MvPolynomial` of total degree ≤ 2, constant and linear terms included; reason: the literal meaning of "polynomial of degree at most two"
-- source:
--   Castro-Silva, Golovnev, Gur, Wolf, A Quadratic Bogolyubov Theorem and Quantum Worst-Case to Average-Case Reductions, STOC 2027 submission (held manuscript, sha256 9d91dee3…), Fact D.2, p.53

import Mathlib
import Definitions.Def_QuadBogolyubov_HasRankAtLeast

set_option autoImplicit false

open scoped BigOperators Pointwise

namespace QuadBogolyubov

/-- **Fact D.2 (Quadratic exponential sums of high rank are small).** Let `q : G → 𝔽₂` be
quadratic, `ℓ : G → 𝔽₂` linear, and suppose `β_q` has rank `r`. Then
`|𝔼_{x∈G}(−1)^{q(x)+ℓ(x)}| ≤ 2^{−r/2}`.

Castro-Silva, Golovnev, Gur, Wolf, *A Quadratic Bogolyubov Theorem and Quantum Worst-Case to
Average-Case Reductions*, STOC 2027 submission (held manuscript, sha256 9d91dee3…), Fact D.2, p.53: "Let q : G → F2 be quadratic, let ℓ : G → F2 be linear, and suppose that βq
has rank r. Then |E_{x∈G}(−1)^{q(x)+ℓ(x)}| ≤ 2^{−r/2}."

**Formalization Note.** `G = 𝔽₂ⁿ`; `β_q` is `bilin q` and its rank is `bilinRank` (the rank of
`h ↦ β_q(h, ·)`, p.52). `ℓ` is a linear functional (`Module.Dual`). -/
theorem fact_D_2 {n : ℕ} (q : (Fin n → ZMod 2) → ZMod 2) (hq : IsQuadraticPoly q)
    (ℓ : Module.Dual (ZMod 2) (Fin n → ZMod 2)) (r : ℕ) (hr : bilinRank (bilin q) = r) :
    |𝔼 x : Fin n → ZMod 2, (-1 : ℝ) ^ (q x + ℓ x).val| ≤ (2 : ℝ) ^ (-((r : ℝ) / 2)) := by sorry

end QuadBogolyubov
