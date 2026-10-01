-- Prove2me | Theorems.Thm_TongString_dedekindEta_neg_inv
-- name    : TongString.dedekindEta_neg_inv
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-25T21:48:29.123727+00:00
-- url     : https://prove2.me/theorems/89d4a164-97dc-40b7-9f99-78906dafdc3a
-- title:
--   $\eta(-1/\tau)=\sqrt{-i\tau}\,\eta(\tau)$
-- statement:
--   For every $\tau\in\mathbb C$ with $\operatorname{Im}\tau>0$, the Dedekind eta function satisfies
--
--   $$
--   \eta(-1/\tau)=\sqrt{-i\tau}\;\eta(\tau),
--   $$
--
--   where $\sqrt{-i\tau}$ is the principal square root (the one with positive real part; note $\operatorname{Re}(-i\tau)=\operatorname{Im}\tau>0$). This is the behaviour of $\eta$ under the modular transformation $S:\tau\mapsto-1/\tau$.
--
--   **Formalization Note** The square root is written as the principal-branch complex power $(-i\tau)^{1/2}$.
-- source:
--   D. Tong, *String Theory*, University of Cambridge Part III Mathematical Tripos lecture notes (January 2009), http://www.damtp.cam.ac.uk/user/tong/string.html, Section 6.4.2, p. 151 ('... and η(−1/τ) = √(−iτ) η(τ)')

import Mathlib
import Definitions.Def_TongString_dedekind_eta

namespace TongString

open Complex

theorem dedekindEta_neg_inv (τ : ℂ) (hτ : 0 < τ.im) :
    dedekindEta (-1 / τ) = (-I * τ) ^ (1 / 2 : ℂ) * dedekindEta τ := by sorry

end TongString
