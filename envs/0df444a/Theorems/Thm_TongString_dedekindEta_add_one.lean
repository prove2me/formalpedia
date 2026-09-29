-- Prove2me | Theorems.Thm_TongString_dedekindEta_add_one
-- name    : TongString.dedekindEta_add_one
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-25T21:47:20.960657+00:00
-- url     : https://prove2.me/theorems/d96a2cf5-7f3e-4894-bff2-7b780d86dde3
-- title:
--   $\eta(\tau+1)=e^{2\pi i/24}\eta(\tau)$
-- statement:
--   For every $\tau\in\mathbb C$ with $\operatorname{Im}\tau>0$, the Dedekind eta function satisfies
--
--   $$
--   \eta(\tau+1)=e^{2\pi i/24}\,\eta(\tau).
--   $$
--
--   This is the behaviour of $\eta$ under the modular transformation $T:\tau\mapsto\tau+1$.
-- source:
--   D. Tong, *String Theory*, University of Cambridge Part III Mathematical Tripos lecture notes (January 2009), http://www.damtp.cam.ac.uk/user/tong/string.html, Section 6.4.2, p. 151 ('The eta-function satisfies the identities η(τ+1) = e^{2πi/24} η(τ) ...')

import Mathlib
import Definitions.Def_TongString_dedekind_eta

namespace TongString

open Complex

theorem dedekindEta_add_one (τ : ℂ) (hτ : 0 < τ.im) :
    dedekindEta (τ + 1) = Complex.exp (2 * Real.pi * I / 24) * dedekindEta τ := by sorry

end TongString
