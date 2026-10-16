-- Prove2me | Theorems.Thm_PersPricingDist_PersonalA_cutoff_order
-- name    : PersPricingDist.PersonalA.cutoff_order
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-16T02:45:12.233167+00:00
-- url     : https://prove2.me/theorems/f2a867b5-1aee-4397-892e-2bd1bab11a7e
-- title:
--   (5), p. 19 and OA p. 13 — the PU cutoff exceeds the PP cutoff
-- statement:
--   For every $s\in(0,1)$, the PU valuation cutoff is strictly larger than the PP cutoff:
--   $$\tilde v(s)<\check v(s).$$
--
--   The inequality identifies the larger range of markets in which mono distribution remains optimal when B must charge a uniform price.
-- source:
--   Jullien, Reisinger & Rey, authors' manuscript of March 2022 (doi:10.1287/mnsc.2022.4437; PDF sha256 25a6c84a…c253), p. 19, (5) (PDF 21); OA p. 13 (PDF 46)

import Mathlib
import Definitions.Def_PersPricingDist_PersonalA_Setting

namespace PersPricingDist.PersonalA

theorem cutoff_order :
    ∀ s ∈ Set.Ioo (0 : ℝ) 1, Model.vTilde s < Model.vCheck s := by sorry

end PersPricingDist.PersonalA
