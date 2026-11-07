-- Prove2me | Theorems.Thm_TrDegJac_lemma_3_22
-- name    : TrDegJac.lemma_3_22
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:37:07.404194+00:00
-- url     : https://prove2.me/theorems/573b11a1-93f9-4c62-9150-35e7874ca5fe
-- title:
--   Lemma 3.22 — a dimension count gives $\mathbb F(f)$-linear dependence
-- statement:
--   Let $f_1,\dots,f_n\in\mathbb F[x_1,\dots,x_n]$ be algebraically independent over $\mathbb F$, let $g_1,\dots,g_m\in\mathbb F[x]$ be arbitrary, and let $V\subseteq\mathbb F[y_1,\dots,y_n]^m$ be a finite-dimensional $\mathbb F$-subspace. Let
--   $$
--   \varphi(A_1,\dots,A_m)=\sum_{i=1}^m A_i(f)\cdot g_i
--   $$
--   and $W=\varphi(V)$. If $\dim_{\mathbb F}V>\dim_{\mathbb F}W$, then $g_1,\dots,g_m$ are linearly dependent over $\mathbb F(f)$.
--
--   This is the linear-algebra engine behind the geometric degree bound (Proposition 3.30).
--
--   Differences from the source:
--   - encoding: V a finite-dimensional vector space of polynomials, dim V > dim W → V a Submodule over F with FiniteDimensional, Module.finrank of V.map φ < Module.finrank of V; reason: both dimensions are finite, so finrank is the dimension
-- source:
--   Forbes and Staicu, Approximating Transcendence Degree in Medium Characteristic, STOC 2027 submission (manuscript sha256 3ab72a42…), Lemma 3.22, p.17

import Mathlib
import Definitions.Def_TrDegJac_RatFn
import Definitions.Def_TrDegJac_adjoinFamily
import Definitions.Def_TrDegJac_evalCombination

set_option autoImplicit false

namespace TrDegJac

/-- **Lemma 3.22** — Forbes and Staicu, *Approximating Transcendence Degree in Medium Characteristic*, STOC 2027
submission (manuscript sha256 3ab72a42…), p.17:
"For f₁, …, f_n ∈ F[x₁, …, x_n] algebraically independent and g₁, …, g_m ∈ F[x] any polynomials.
Let V ⊆ F[y]^m be a finite dimensional vector space of polynomials. Consider the linear map
φ : F[y]^m → F[x] defined by (A₁, …, A_m) ↦ ∑_{i=1}^m A_i(f) · g_i. Let W = φ(V) so that W is a
finite-dimensional vector space. If dim V > dim W then the polynomials g₁, …, g_m are
F(f)-linearly dependent."

**Formalization Note.** `F[y] = F[y₁, …, y_n]` is `MvPolynomial (Fin n) F` (one variable `y_i` per
`f_i`), `V` is an `F`-subspace of `F[y]^m`, `φ` is `evalCombination f g`, and `W` is the image
`V.map φ`. Dimensions are `Module.finrank` over `F`, both finite because `V` is. Linear dependence
of the `g_i` is over the subfield `F(f)` of `F(x)`. -/
theorem lemma_3_22 {F : Type*} [Field F] {n m : ℕ} (f : Fin n → MvPolynomial (Fin n) F)
    (hf : AlgebraicIndependent F f) (g : Fin m → MvPolynomial (Fin n) F)
    (V : Submodule F (Fin m → MvPolynomial (Fin n) F)) (hV : FiniteDimensional F V)
    (hdim : Module.finrank F (V.map (evalCombination f g)) < Module.finrank F V) :
    ¬ LinearIndependent (adjoinFamily f) (fun i => toRatFn (g i)) := by sorry

end TrDegJac
