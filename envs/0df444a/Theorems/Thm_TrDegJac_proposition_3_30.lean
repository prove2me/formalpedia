-- Prove2me | Theorems.Thm_TrDegJac_proposition_3_30
-- name    : TrDegJac.proposition_3_30
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:37:10.463171+00:00
-- url     : https://prove2.me/theorems/d62a0251-a002-4efe-9f00-f8d71d929d2d
-- title:
--   Proposition 3.30 — geometric degree bound $[\mathbb F(x):\mathbb F(f)]\le\prod_i\deg f_i$
-- statement:
--   Let $f_1,\dots,f_n\in\mathbb F[x_1,\dots,x_n]$ be algebraically independent over $\mathbb F$. Then $\mathbb F(x)$ is a finite extension of $\mathbb F(f)$ and
--   $$
--   [\mathbb F(x):\mathbb F(f)]\ \le\ \prod_{i=1}^n\deg f_i .
--   $$
--
--   This Bézout-type bound, valid in every characteristic, controls the tower of fields in the proof of Theorem 4.12 (through Lemma 4.11).
--
--   **Formalization Note** $\deg$ is the total degree. The field degree is `Module.rank`, a cardinal, so the bound also asserts finiteness; a `Module.finrank` bound would hold vacuously on an infinite extension.
--
--   Differences from the source:
--   - encoding: [F(x) : F(f)] ≤ ∏ deg f_i → Module.rank of F(x) over the intermediate field F(f), as a cardinal, ≤ the natural number ∏ totalDegree (f i); reason: the paper's degree is the vector-space dimension; a cardinal bound by a natural number is the same statement, including the finiteness the paper uses on p.28
-- source:
--   Forbes and Staicu, Approximating Transcendence Degree in Medium Characteristic, STOC 2027 submission (manuscript sha256 3ab72a42…), Proposition 3.30, p.21

import Mathlib
import Definitions.Def_TrDegJac_RatFn
import Definitions.Def_TrDegJac_adjoinFamily

set_option autoImplicit false

namespace TrDegJac

/-- **Proposition 3.30 (geometric degree bound)** — Forbes and Staicu, *Approximating Transcendence Degree in Medium Characteristic*, STOC 2027
submission (manuscript sha256 3ab72a42…), p.21:
"For f₁, …, f_n ∈ F[x₁, …, x_n] algebraically independent, [F(x) : F(f)] ≤ ∏_{i=1}^n deg f_i."

**Formalization Note.** `deg` is `MvPolynomial.totalDegree`. The degree `[F(x) : F(f)]` is
`Module.rank` of `F(x)` over the intermediate field `F(f)`, a cardinal; the bound by a natural
number therefore also asserts that the extension is finite (a `Module.finrank` bound would hold
vacuously on an infinite extension). -/
theorem proposition_3_30 {F : Type*} [Field F] {n : ℕ} (f : Fin n → MvPolynomial (Fin n) F)
    (hf : AlgebraicIndependent F f) :
    Module.rank (adjoinFamily f) (RatFn F n) ≤ ((∏ i, (f i).totalDegree : ℕ) : Cardinal) := by sorry

end TrDegJac
