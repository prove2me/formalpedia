-- Prove2me | Theorems.Thm_SU2Eposic_Extreme_theorem_2_7
-- name    : SU2Eposic.Extreme.theorem_2_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T09:28:58.215994+00:00
-- url     : https://prove2.me/theorems/19a39b4e-521e-4edf-a0a0-031cb3ae86b0
-- title:
--   Theorem 2.7 — decomposition identity for bi-degree polynomials
-- statement:
--   Let $m,n\in\mathbb N$ and let $f(x,y)$ be a polynomial in $x=(x_1,x_2)$, $y=(y_1,y_2)$ of bi-degree $(m,n)$, i.e. homogeneous of degree $m$ in $x$ and of degree $n$ in $y$. With the operators $\Gamma_{xy},\Delta_{yx},\Delta_{xy},\Omega_{xy}$ and the coefficients $c_{m,n,h}$ (defined by the recursion $c_{m,0,0}=1$, and for $n\ge1$ $c_{m,n,h}=\frac{1}{(m+1)n}c_{m+1,n-1,h}$ if $h=0$, $\frac{1}{(m+1)n}[c_{m-1,n-1,h-1}+c_{m+1,n-1,h}]$ if $0<h<n$, $\frac{1}{(m+1)n}c_{m-1,n-1,h-1}$ if $h=n$),
--   $$f(x,y)=\sum_{h=0}^{\min\{m,n\}}c_{m,n,h}\,\Gamma_{xy}^h\Delta_{yx}^{n-h}\Delta_{xy}^{n-h}\Omega_{xy}^h\big(f(x,y)\big).$$
--
--   This identity, cited in the paper from Procesi's *Lie groups* (Chapter 3), is the polynomial form of the Clebsch–Gordan decomposition $P_m\otimes P_n\cong\bigoplus_h P_{m+n-2h}$; it is what makes the maps $\alpha_{m,n,h}$ isometries that together resolve the identity.
--
--   **Formalization Note** $f$ is an element of `MvPolynomial (Fin 4) ℂ`; bi-degree $(m,n)$ is the hypothesis that every monomial $x_1^{s_0}x_2^{s_1}y_1^{s_2}y_2^{s_3}$ of $f$ has $s_0+s_1=m$ and $s_2+s_3=n$. The coefficients $c_{m,n,h}$ are the real numbers given by the recursion, cast to $\mathbb C$.
-- source:
--   Al Nuwairan, SU(2)-irreducibly covariant and EPOSIC channels, arXiv:1306.5321v1, p. 11, Theorem 2.7 (cited from Procesi [12, chp. 3])

import Mathlib
import Definitions.Def_SU2Eposic_Extreme_Setup

namespace SU2Eposic.Extreme

open MvPolynomial

/-- **Theorem 2.7, p. 11** (cited in the paper from Procesi [12, chp. 3]). Every polynomial
`f(x, y)` of bi-degree `(m, n)` satisfies
`f = Σ_{h=0}^{min{m,n}} c_{m,n,h} Γ^h_xy ∆^{n−h}_yx ∆^{n−h}_xy Ω^h_xy f`. Bi-degree `(m, n)`: every
monomial of `f` has degree `m` in `x₁, x₂` and degree `n` in `y₁, y₂`. -/
theorem theorem_2_7 (m n : ℕ) (f : Poly)
    (hf : ∀ s ∈ f.support, s 0 + s 1 = m ∧ s 2 + s 3 = n) :
    f = ∑ h ∈ Finset.range (min m n + 1),
      ((c m n h : ℝ) : ℂ) • (gammaXY ^ h) ((deltaYX ^ (n - h)) ((deltaXY ^ (n - h)) ((omegaXY ^ h) f))) := by sorry

end SU2Eposic.Extreme
