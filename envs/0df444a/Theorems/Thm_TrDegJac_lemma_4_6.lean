-- Prove2me | Theorems.Thm_TrDegJac_lemma_4_6
-- name    : TrDegJac.lemma_4_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:36:00.825344+00:00
-- url     : https://prove2.me/theorems/a5816a19-16e2-446a-99d6-9f57d118b5ca
-- title:
--   Lemma 4.6 — chain rule $\mathrm{Jac}_x(g(f))=\mathrm{Jac}_x(f)\cdot\mathrm{Jac}_y(g)(f)$
-- statement:
--   Let $f_1,\dots,f_m\in\mathbb F[x_1,\dots,x_n]$ and $g\in\mathbb F[y_1,\dots,y_m]$. Then $\mathrm{Jac}_x(g(f))=\mathrm{Jac}_x(f)\cdot\mathrm{Jac}_y(g)(f)$; entrywise, for every $i\in\{1,\dots,n\}$,
--   $$
--   \frac{\partial\, g(f)}{\partial x_i}=\sum_{j=1}^m\frac{\partial f_j}{\partial x_i}\cdot\Big(\frac{\partial g}{\partial y_j}\Big)(f).
--   $$
--
--   The chain rule turns an annihilator of $f$ into a linear relation among the columns of $\mathrm{Jac}_x(f)$ (Proposition 4.7, Theorem 4.12).
--
--   Differences from the source:
--   - encoding: the n × 1 matrix identity Jac_x(g(f)) = Jac_x(f) · Jac_y(g)(f) → the identity of entries i = 1, …, n in F[x]; reason: a matrix identity is the identity of its entries
-- source:
--   Forbes and Staicu, Approximating Transcendence Degree in Medium Characteristic, STOC 2027 submission (manuscript sha256 3ab72a42…), Lemma 4.6, p.26

import Mathlib

set_option autoImplicit false

namespace TrDegJac

/-- **Lemma 4.6 (chain rule)** — Forbes and Staicu, *Approximating Transcendence Degree in Medium Characteristic*, STOC 2027
submission (manuscript sha256 3ab72a42…), p.26:
"Let f₁, …, f_m ∈ F[x] and g ∈ F[y₁, …, y_m] then Jac_x(g(f)) = Jac_x(f) · Jac_y(g)(f)."

Entry `i` of the `n × 1` matrix identity reads
`∂_{x_i}(g(f)) = ∑_{j=1}^m ∂_{x_i}(f_j) · (∂_{y_j} g)(f)`.

**Formalization Note.** Stated entrywise, as an identity in `F[x] = MvPolynomial (Fin n) F`;
`g(f)` is `MvPolynomial.aeval f g` and `∂` is `MvPolynomial.pderiv`. -/
theorem lemma_4_6 {F : Type*} [Field F] {n m : ℕ} (f : Fin m → MvPolynomial (Fin n) F)
    (g : MvPolynomial (Fin m) F) (i : Fin n) :
    MvPolynomial.pderiv i (MvPolynomial.aeval f g) =
      ∑ j, MvPolynomial.pderiv i (f j) * MvPolynomial.aeval f (MvPolynomial.pderiv j g) := by sorry

end TrDegJac
