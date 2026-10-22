-- Prove2me | Theorems.Thm_PetruzziDada_Additive_eq_5
-- name    : PetruzziDada.Additive.eq_5
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-20T15:49:07.442889+00:00
-- url     : https://prove2.me/theorems/8b8fbdac-3685-42ec-83c3-68e3cc98d52c
-- title:
--   Eq. (5) — ∂E[Π(z, p)]/∂z = −(c + h) + (p + s + h)[1 − F(z)]
-- statement:
--   In the additive-demand price-setting newsvendor, fix any real price $p$. The expected profit $z \mapsto E[\Pi(z,p)]$ (the integral of p. 184) is differentiable at every real stocking factor $z$, with
--   $$\frac{\partial E[\Pi(z,p)]}{\partial z} = -(c+h) + (p+s+h)[1-F(z)],$$
--   where $F(z) = \int_A^z f(u)\,du$ is the distribution function of the demand noise.
--
--   This is eq. (5) of the paper, the first-order condition in $z$ that yields the newsvendor fractile $1 - F(z^*) = (c+h)/(p+s+h)$ for a fixed price.
--
--   **Formalization Note** The density $f$ is only assumed integrable (no continuity), and the derivative is claimed at every real $z$, including $z = A$, $z = B$ and points outside $[A,B]$.
-- source:
--   Petruzzi & Dada, Pricing and the Newsvendor Problem: A Review with Extensions, Oper. Res. 47(2) 1999, p. 184, eq. (5)

import Mathlib
import Definitions.Def_PetruzziDada_Additive_Model

open MeasureTheory

namespace PetruzziDada.Additive

/-- Eq. (5), p. 184: `∂E[Π(z, p)]/∂z = -(c + h) + (p + s + h)[1 - F(z)]`, at every `z`
and every price `p`. -/
theorem eq_5 (M : Model) (z p : ℝ) :
    HasDerivAt (fun z' => M.expProfit z' p) (-(M.c + M.h) + (p + M.s + M.h) * (1 - M.F z)) z := by sorry
end PetruzziDada.Additive
