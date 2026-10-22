-- Prove2me | Theorems.Thm_PetruzziDada_Additive_eq_1
-- name    : PetruzziDada.Additive.eq_1
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-20T15:49:09.743518+00:00
-- url     : https://prove2.me/theorems/1f2e26c3-a811-46b6-ab5e-3ea91fc236bf
-- title:
--   Eqs. (1)–(3) — expected profit = riskless profit Ψ(p) minus expected loss L(z, p)
-- statement:
--   In the additive-demand price-setting newsvendor (demand $a - bp + \varepsilon$, with $\varepsilon$ having density $f$ on $[A,B]$, mean $\mu$ and distribution function $F$; stocking factor $z$, so that $q = y(p) + z$ units are stocked), let
--   $$\Lambda(z) = \int_A^z (z-u) f(u)\,du, \qquad \Theta(z) = \int_z^B (u-z) f(u)\,du$$
--   be the expected leftovers and expected shortages. Then for every real stocking factor $z$ and every real price $p$, the expected profit
--   $$E[\Pi(z,p)] = \int_A^z \big(p[y(p)+u] - h[z-u]\big) f(u)\,du + \int_z^B \big(p[y(p)+z] - s[u-z]\big) f(u)\,du - c[y(p)+z]$$
--   decomposes as
--   $$E[\Pi(z,p)] = \Psi(p) - L(z,p), \qquad \Psi(p) = (p-c)[y(p)+\mu], \qquad L(z,p) = (c+h)\Lambda(z) + (p+s-c)\Theta(z).$$
--
--   This is the paper's eq. (1), with (2) and (3) defining its two terms: expected profit is the **riskless profit** of the certainty-equivalent problem less the **expected loss** from overage cost $c+h$ and underage cost $p+s-c$. Every later computation (eqs. (5)–(8), Lemma 1, Theorem 1) starts from it.
-- source:
--   Petruzzi & Dada, Pricing and the Newsvendor Problem: A Review with Extensions, Oper. Res. 47(2) 1999, p. 184, eqs. (1)–(3)

import Mathlib
import Definitions.Def_PetruzziDada_Additive_Model

open MeasureTheory

namespace PetruzziDada.Additive

/-- Eqs. (1)–(3), p. 184: the expected-profit integral equals the riskless profit less the
expected loss, `E[Π(z, p)] = Ψ(p) - L(z, p)`, for every stocking factor `z` and price `p`. -/
theorem eq_1 (M : Model) (z p : ℝ) : M.expProfit z p = M.Ψ p - M.L z p := by sorry
end PetruzziDada.Additive
