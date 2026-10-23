-- Prove2me | Theorems.Thm_PersPricingDist_PersonalA_pu_cutoff
-- name    : PersPricingDist.PersonalA.pu_cutoff
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-16T02:45:13.591991+00:00
-- url     : https://prove2.me/theorems/977a4bb2-969d-4a32-a7b0-dcad5a17acb8
-- title:
--   (28), OA p. 11 — PU dual distribution iff v exceeds the cutoff
-- statement:
--   Let $0<s<v<1$ and $X\ge v/s$. When B charges one uniform retail price before A responds with personalized prices, dual distribution yields a strict increase in industry profit precisely when
--   $$v>\check v(s):=\frac{s}{1+s}\left(2+\sqrt{\frac{(1-s)(2+5s+s^2)}{1+2s}}\right).$$
--
--   The statement compares the equilibrium continuation profit, including B's global retail-price choice, with A's personalized monopoly profit.
--
--   **Formalization Note** Display (28) prints a weak inequality, but at equality the profits tie. Footnote 17 and Proposition 4 require a strict gain, hence the strict inequality here. At a wholesale price with several maximizing retail prices, the definition asks whether one yields the gain.
-- source:
--   Jullien, Reisinger & Rey, authors' manuscript of March 2022 (doi:10.1287/mnsc.2022.4437; PDF sha256 25a6c84a…c253), OA pp. 11–12, (28) (PDF 44–45)

import Mathlib
import Definitions.Def_PersPricingDist_PersonalA_Setting

namespace PersPricingDist.PersonalA

theorem pu_cutoff (M : Model) (hM : M.Standing) :
    M.DualPU ↔ Model.vCheck M.s < M.v := by sorry

end PersPricingDist.PersonalA
