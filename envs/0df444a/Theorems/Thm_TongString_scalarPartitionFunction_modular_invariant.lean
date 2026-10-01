-- Prove2me | Theorems.Thm_TongString_scalarPartitionFunction_modular_invariant
-- name    : TongString.scalarPartitionFunction_modular_invariant
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-25T21:55:47.843037+00:00
-- url     : https://prove2.me/theorems/e4e04ee4-c45f-4a2f-b45e-c0b304dd5f43
-- title:
--   The scalar partition function $Z_{\rm scalar}=(\operatorname{Im}\tau)^{-1/2}|\eta|^{-2}$ is modular invariant
-- statement:
--   Let $Z_{\text{scalar}}(\tau)=\dfrac{1}{\sqrt{\operatorname{Im}\tau}}\dfrac{1}{|\eta(\tau)|^2}$ be the partition function (6.20) of a free scalar field on the torus (constant factors dropped). Then for all $a,b,c,d\in\mathbb Z$ with $ad-bc=1$ and every $\tau$ with $\operatorname{Im}\tau>0$,
--
--   $$
--   Z_{\text{scalar}}\!\left(\frac{a\tau+b}{c\tau+d}\right)=Z_{\text{scalar}}(\tau).
--   $$
--
--   Tong notes that the two eta identities "ensure that the scalar partition function (6.20) is a modular invariant function".
-- source:
--   D. Tong, *String Theory*, University of Cambridge Part III Mathematical Tripos lecture notes (January 2009), http://www.damtp.cam.ac.uk/user/tong/string.html, Section 6.4.2, p. 151 ('These two statements ensure that the scalar partition function (6.20) is a modular invariant function.')

import Mathlib
import Definitions.Def_TongString_modular_action
import Definitions.Def_TongString_partition_functions

namespace TongString

theorem scalarPartitionFunction_modular_invariant (a b c d : ℤ) (h : a * d - b * c = 1) (τ : ℂ)
    (hτ : 0 < τ.im) :
    scalarPartitionFunction (modularAction a b c d τ) = scalarPartitionFunction τ := by sorry

end TongString
