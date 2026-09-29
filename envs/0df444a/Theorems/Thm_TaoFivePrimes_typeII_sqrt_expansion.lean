-- Prove2me | Theorems.Thm_TaoFivePrimes_typeII_sqrt_expansion
-- name    : TaoFivePrimes.typeII_sqrt_expansion
-- status  : Proved
-- author  : @Hartmann_Psi
-- created : 2026-09-14T05:03:44.131535+00:00
-- url     : https://prove2.me/theorems/09bcfa41-19d6-485e-8e7b-52d337da113b
-- title:
--   Tao Section 5: expanding the Type II product by $\sqrt{a+b}\le\sqrt a+\sqrt b$
-- statement:
--   For positive reals $x,W,q$,
--
--   $$\sqrt{\frac W4+2q}\;\sqrt{\frac{x}{2Wq}+1}\;\sqrt x\ \le\ \frac{1}{2\sqrt2}\frac{x}{\sqrt q}+\frac12\sqrt{xW}+\frac{x}{\sqrt W}+\sqrt2\,\sqrt{xq}.$$
--
--   This is the step in the source's Type II estimate that turns the pointwise bound on the dyadic bilinear sums,
--   $$F(W)\le\frac{1.1}{8}\Bigl(\frac W4+2q\Bigr)^{1/2}\Bigl(\frac{x}{2Wq}+1\Bigr)^{1/2}x^{1/2}\log W,$$
--   into a sum of four terms, each of which can be integrated separately against $\frac{dW}{W}$ over the range $V\le W\le x/U$. The mechanism is the subadditivity $\sqrt{a+b}\le\sqrt a+\sqrt b$ applied to both brackets, followed by multiplying out; the four resulting products are, in order, $\frac{x}{2\sqrt2\sqrt q}$, $\frac12\sqrt{xW}$, $\frac{x}{\sqrt W}$ and $\sqrt{2xq}$. Note that $\sqrt2\sqrt{xq}=\sqrt2\,x/\sqrt{x/q}$, which is the form in which the source writes the last term.
--
--   **Deviation from the source** The source records the third term as $\frac1{\sqrt2}\frac{x}{\sqrt W}$. Expanding the product gives $\sqrt{2q}\cdot\sqrt{\frac{x}{2Wq}}\cdot\sqrt x=x\sqrt{\frac{2q}{2Wq}}=\frac{x}{\sqrt W}$, without the factor $\frac1{\sqrt2}$; the coefficient above is the one the expansion actually produces.
-- source:
--   Terence Tao, "Every odd number greater than 1 is the sum of at most five primes", Mathematics of Computation 83 (2014), 997-1038; arXiv:1201.6656, https://arxiv.org/abs/1201.6656, Section 5 (Minor arcs), subsection "Estimation of the Type II sum", the display beginning "Crudely bounding (a+b)^{1/2} <= a^{1/2} + b^{1/2}"; the third coefficient is corrected, see the Deviation note

import Mathlib

theorem TaoFivePrimes.typeII_sqrt_expansion (x W q : ℝ) (hx : 0 < x) (hW : 0 < W) (hq : 0 < q) :
    Real.sqrt (W / 4 + 2 * q) * Real.sqrt (x / (2 * W * q) + 1) * Real.sqrt x
      ≤ (1 / (2 * Real.sqrt 2)) * (x / Real.sqrt q) + (1 / 2) * Real.sqrt (x * W)
        + x / Real.sqrt W + Real.sqrt 2 * Real.sqrt (x * q) := by sorry
