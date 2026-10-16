-- Prove2me | Theorems.Thm_PersPricingDist_PersonalA_pp_cutoff
-- name    : PersPricingDist.PersonalA.pp_cutoff
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T02:45:15.079155+00:00
-- url     : https://prove2.me/theorems/b8c9cec3-e00b-43b2-931b-bd9be4257a70
-- title:
--   (4), p. 18 — PP dual distribution iff v exceeds the cutoff
-- statement:
--   Let $0<s<v<1$ and $X\ge v/s$. When both A and B set personalized prices, dual distribution yields a strict increase in industry profit precisely when
--   $$v>\tilde v(s):=\frac{s(2+\sqrt{1-s})}{1+s}. $$
--
--   This connects the market outcome, optimized over nonnegative wholesale prices, to the valuation cutoff in display (4).
--
--   **Formalization Note** A strict increase is required by footnote 17; the proposition includes all admissible $s$, including those for which the cutoff exceeds $1$.
-- source:
--   Jullien, Reisinger & Rey, authors' manuscript of March 2022 (doi:10.1287/mnsc.2022.4437; PDF sha256 25a6c84a…c253), p. 18, (4) (PDF 20); OA p. 7 (PDF 40)

import Mathlib
import Definitions.Def_PersPricingDist_PersonalA_Setting

namespace PersPricingDist.PersonalA

theorem pp_cutoff (M : Model) (hM : M.Standing) :
    M.DualPP ↔ Model.vTilde M.s < M.v := by sorry

end PersPricingDist.PersonalA
