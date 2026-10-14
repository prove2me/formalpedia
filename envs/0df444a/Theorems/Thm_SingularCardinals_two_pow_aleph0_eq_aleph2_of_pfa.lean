-- Prove2me | Theorems.Thm_SingularCardinals_two_pow_aleph0_eq_aleph2_of_pfa
-- name    : SingularCardinals.two_pow_aleph0_eq_aleph2_of_pfa
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-11T14:51:09.05896+00:00
-- url     : https://prove2.me/theorems/d7eb87a8-286d-4468-b5c7-bfa2534a6f4a
-- title:
--   PFA implies 2^ℵ₀ = ℵ₂
-- statement:
--   Assume the proper forcing axiom (PFA). Then the continuum is $\aleph_2$:
--   $$2^{\aleph_0}=\aleph_2.$$
--
--   In particular PFA is incompatible with the continuum hypothesis, and hence with GCH; this is why the source presents PFA as a hypothesis implying SCH by a route entirely different from GCH.
-- source:
--   Wikipedia, "Singular cardinals hypothesis", revision oldid=1349753131, https://en.wikipedia.org/w/index.php?title=Singular_cardinals_hypothesis&oldid=1349753131, last paragraph: "the proper forcing axiom, which implies 2^ℵ0 = ℵ2 and hence is incompatible with GCH".

import Mathlib
import Definitions.Def_JechStationary
import Definitions.Def_SingularCardinals_basic
import Definitions.Def_SingularCardinals_PFA

universe u

open Cardinal

namespace SingularCardinals

theorem two_pow_aleph0_eq_aleph2_of_pfa (h : PFA.{u}) :
    (2 : Cardinal.{u}) ^ ℵ₀ = aleph 2 := by sorry

end SingularCardinals
