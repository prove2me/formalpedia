-- Prove2me | Theorems.Thm_TongString_stringPartitionIntegrand_modular_invariant
-- name    : TongString.stringPartitionIntegrand_modular_invariant
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-25T22:29:58.492975+00:00
-- url     : https://prove2.me/theorems/38e8ce82-a59c-4a1f-98dc-66a256d5661c
-- title:
--   The one-loop string integrand $(\operatorname{Im}\tau)^{-12}|\eta(\tau)|^{-48}$ is modular invariant
-- statement:
--   Let $\eta$ be the Dedekind eta function and let
--
--   $$
--   F(\tau)=\left(\frac{1}{\sqrt{\operatorname{Im}\tau}}\,\frac{1}{\eta(\tau)\,\overline{\eta(\tau)}}\right)^{24}=\frac{1}{(\operatorname{Im}\tau)^{12}\,|\eta(\tau)|^{48}}
--   $$
--
--   be the integrand of the bosonic string one-loop partition function $Z_{\text{string}}=\int\frac{d^2\tau}{(\operatorname{Im}\tau)^2}F(\tau)$. Then for all $a,b,c,d\in\mathbb Z$ with $ad-bc=1$ and every $\tau$ with $\operatorname{Im}\tau>0$,
--
--   $$
--   F\!\left(\frac{a\tau+b}{c\tau+d}\right)=F(\tau).
--   $$
--
--   Together with the invariance of the measure $d^2\tau/(\operatorname{Im}\tau)^2$, this is Tong's statement that "both the measure and the integrand are individually modular invariant", which makes the integral over the fundamental domain well defined.
--
--   **Formalization Note** Constant prefactors that Tong neglects (powers of $\alpha'$) are omitted; they do not affect invariance.
-- source:
--   D. Tong, *String Theory*, University of Cambridge Part III Mathematical Tripos lecture notes (January 2009), http://www.damtp.cam.ac.uk/user/tong/string.html, Section 6.4.2, p. 151 (Z_string written in terms of η; 'Both the measure and the integrand, are individually modular invariant.')

import Mathlib
import Definitions.Def_TongString_modular_action
import Definitions.Def_TongString_partition_functions

namespace TongString

theorem stringPartitionIntegrand_modular_invariant (a b c d : ℤ) (h : a * d - b * c = 1)
    (τ : ℂ) (hτ : 0 < τ.im) :
    stringPartitionIntegrand (modularAction a b c d τ) = stringPartitionIntegrand τ := by sorry

end TongString
