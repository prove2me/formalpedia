-- Prove2me | Theorems.Thm_TongString_riemannZeta_neg_one
-- name    : TongString.riemannZeta_neg_one
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-25T20:52:09.623878+00:00
-- url     : https://prove2.me/theorems/1eeb82f2-40b4-4088-85f4-a43a1c7446c2
-- title:
--   $\zeta(-1)=-\frac1{12}$
-- statement:
--   The Riemann zeta function, defined by $\zeta(s)=\sum_{n\ge1}n^{-s}$ for $\operatorname{Re}s>1$ and extended by analytic continuation, satisfies
--
--   $$
--   \zeta(-1)=-\frac{1}{12}.
--   $$
--
--   This is the "zeta-function regularization" of the zero-point sum $\sum_{n\ge1}n$, giving the normal-ordering constant $a=\frac{D-2}{24}$.
--
--   **Formalization Note** `riemannZeta` is Mathlib's meromorphic continuation of the zeta function to $\mathbb C$.
-- source:
--   D. Tong, *String Theory*, University of Cambridge Part III Mathematical Tripos lecture notes (January 2009), http://www.damtp.cam.ac.uk/user/tong/string.html, Section 2.2.2 'Zeta Function Regularization', p. 40

import Mathlib

namespace TongString

theorem riemannZeta_neg_one : riemannZeta (-1) = -1 / 12 := by sorry

end TongString
