-- Prove2me | Theorems.Thm_RandomOrderCRS_proposition_10
-- name    : RandomOrderCRS.proposition_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:21:07.003245+00:00
-- url     : https://prove2.me/theorems/e950659f-7df0-4ca4-b3f5-2871d4a94005
-- title:
--   Proposition 10 — vertex-splitting properties of $a_1$
-- statement:
--   Let $a=a_1$ and $x_1,x_2\in[0,1]$. Then:
--
--   1. $y\mapsto\ell(x_1,y)\ell(x_2,y)-\exp(-(x_1+x_2)y)$ is non-negative for $y\in[0,1]$;
--   2. if $x_1+x_2\le1$, the function
--   $$\phi(y):=\ell(x_1,y)\ell(x_2,y)+T(x_1+x_2,y)\big(y\,s(x_1)\ell(x_2,y)+y\,s(x_2)\ell(x_1,y)\big)-e^{-(x_1+x_2)y}\left(1+\frac{(x_1+x_2)a(1)y^2}{2}\right)$$
--   is initially non-negative for $y\in[0,1]$ and changes sign at most once, and its integral over $[0,1]$ is non-negative.
--
--   Here $a(1)=a_1(1)=(e-2)^2$ is a constant. These two properties are the input of the vertex-splitting Lemma 4.
--
--   Differences from the source:
--   - reading: for all $x_1,x_2\in[0,1]$ in item 2 → item 2 assumes $x_1+x_2\le1$; reason: $T(x_1+x_2,y)$ contains $s(1-x_1-x_2)$ and $a$ is defined only on $[0,1]$, so the printed item has no meaning otherwise; extending $a_1$ as a polynomial makes it false (integral about $-0.00995$ at $x_1=x_2=0.9$), and its only use has $x_1+x_2\le1$ by the degree constraint
--   - encoding: initially non-negative, and changes sign at most once → there is $z_c\in[0,1]$ with $\phi\ge0$ on $[0,z_c]$ and $\phi\le0$ on $[z_c,1]$; reason: this is the hypothesis of Proposition 11, the only use
--   - encoding: $T$ with the printed formula → $T$ through $\tau$; reason: it equals the printed formula for $xy\ne0$ and its limits at $xy=0$
-- source:
--   MacRury, Ma & Grammel, On (Random-order) Online Contention Resolution Schemes for the Matching Polytope of (Bipartite) Graphs, arXiv:2209.07520v2, Proposition 10, p.21; §C.7, ec19–ec20

import Mathlib
import Definitions.Def_RandomOrderCRS_Attenuation

open Real

namespace RandomOrderCRS

/-- Proposition 10 (Vertex splitting), MacRury, Ma & Grammel, arXiv:2209.07520v2, p.21, for
`a = a₁` (§C.7, ec19): for all `x₁, x₂ ∈ [0, 1]`,
1. `y → ℓ(x₁, y) ℓ(x₂, y) − exp(−(x₁ + x₂)y)` is non-negative for `y ∈ [0, 1]`;
2. the function `φ(y) := ℓ(x₁, y) ℓ(x₂, y) + T(x₁ + x₂, y)(y s(x₁) ℓ(x₂, y) + y s(x₂) ℓ(x₁, y))
   − e^{−(x₁+x₂)y}(1 + (x₁ + x₂) a(1) y²/2)` is initially non-negative for `y ∈ [0, 1]`, and changes
   sign at most once; moreover, its integral over `[0, 1]` is non-negative.

**Formalization Note.** Item 2 carries `x₁ + x₂ ≤ 1`. The function `T(x₁ + x₂, y)` contains
`s(1 − x₁ − x₂)`, and `a` is defined only on `[0, 1]`, so the printed item 2 has no meaning without
it; the polynomial extension of `a₁` makes it false (integral ≈ −0.00995 at `x₁ = x₂ = 0.9`). The
only use of item 2, on ec19, has `x₁ + x₂ ≤ 1` by the degree constraint at `w`. "Initially
non-negative, changes sign at most once" is: there is `z_c ∈ [0, 1]` with `φ ≥ 0` on `[0, z_c]` and
`φ ≤ 0` on `[z_c, 1]`, which is the hypothesis of Proposition 11. -/
theorem proposition_10 (x₁ x₂ : ℝ) (h₁ : x₁ ∈ Set.Icc (0 : ℝ) 1) (h₂ : x₂ ∈ Set.Icc (0 : ℝ) 1) :
    (∀ y ∈ Set.Icc (0 : ℝ) 1, 0 ≤ ell a₁ x₁ y * ell a₁ x₂ y - exp (-(x₁ + x₂) * y)) ∧
    (x₁ + x₂ ≤ 1 →
      let φ : ℝ → ℝ := fun y =>
        ell a₁ x₁ y * ell a₁ x₂ y +
          T a₁ (x₁ + x₂) y * (y * survival a₁ x₁ * ell a₁ x₂ y + y * survival a₁ x₂ * ell a₁ x₁ y) -
          exp (-(x₁ + x₂) * y) * (1 + (x₁ + x₂) * a₁ 1 * y ^ 2 / 2)
      (∃ zc ∈ Set.Icc (0 : ℝ) 1,
        (∀ y ∈ Set.Icc 0 zc, 0 ≤ φ y) ∧ ∀ y ∈ Set.Icc zc 1, φ y ≤ 0) ∧
      0 ≤ ∫ y in (0 : ℝ)..1, φ y) := by sorry

end RandomOrderCRS
