-- Prove2me | Theorems.Thm_SuperTableaux_JacobiTrudi_eq_3_14_finite
-- name    : SuperTableaux.JacobiTrudi.eq_3_14_finite
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:29:30.312279+00:00
-- url     : https://prove2.me/theorems/53a6865e-da12-48d8-aea5-f8860c4b2fd8
-- title:
--   (3.14), p. 18 — each coefficient of $S^{\mathcal A/\mathcal B}_\lambda$ counts finitely many tableaux
-- statement:
--   Let $\mathcal A,\mathcal B$ be linearly ordered, at most countable, $\mathbb Z_2$-graded sets, $n\ge1$ and $\lambda\in\mathbb Z^n_+$. For every monomial $x_{\mathcal A}^{\alpha}(x_{\mathcal B}^{\beta})^{-1}$, the set
--   $$\{(T^+,T^-)\in SST_{\mathcal A/\mathcal B}(\lambda)\;:\;\mathrm{wt}(T^+)=\alpha,\ \mathrm{wt}(T^-)=\beta\}$$
--   is finite.
--
--   This is the content of the paper's remark that $S^{\mathcal A/\mathcal B}_\lambda$ is a well-defined element of $\mathbb Z[[x_{\mathcal A},x_{\mathcal B}^{-1}]]$: every coefficient of the generating function (3.14) is a finite count. It guarantees that the coefficients of the characters used throughout the mission are genuine counts.
--
--   **Formalization Note** The ring $\mathbb Z[[x_{\mathcal A},x_{\mathcal B}^{-1}]]$ is `MvPowerSeries (A ⊕ B) ℤ`: the variable `Sum.inl a` is $x_a$ and the variable `Sum.inr b` is the symbol $x_b^{-1}$, so a monomial with exponent vector $m$ is $\prod_a x_a^{m(a)}\prod_b (x_b^{-1})^{m(b)}$; this is literally a power-series ring in the symbols $x_a$ and $x_b^{-1}$. A/B-tableaux are encoded in cut coordinates (see the definitions item).
-- source:
--   Kwon, Rational semistandard tableaux and character formula for the Lie superalgebra ĝl∞|∞, arXiv:math/0605005v1, p. 18, (3.14) and the remark after it

import Mathlib
import Definitions.Def_SuperTableaux_JacobiTrudi_Setting

namespace SuperTableaux.JacobiTrudi
theorem eq_3_14_finite {A B : Type*} [LinearOrder A] [Countable A] [LinearOrder B] [Countable B]
    (oddA : A → Bool) (oddB : B → Bool) (n : ℕ) (hn : 0 < n) (la : GenPartition n)
    (m : (A ⊕ B) →₀ ℕ) :
    Finite {X : ABTab oddA oddB la // wtAB X = m} := by sorry
end SuperTableaux.JacobiTrudi
