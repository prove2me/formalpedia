-- Prove2me | Theorems.Thm_SolarTariff_Fair_T3_threshold
-- name    : SolarTariff.Fair.T3_threshold
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:32:20.51558+00:00
-- url     : https://prove2.me/theorems/15e3d31d-0cf8-4e91-bcc1-d4545f117e48
-- title:
--   §4.3, p. 18 — adoption threshold under T3
-- statement:
--   Under a tariff $T_3$ with common retail rate $p_r$ and adopting-tier fixed fee $f_i$, a tier with $g_i>0$ has adoption threshold
--
--   $$t(i)=p_r-\frac{f_i}{g_i}.$$
--
--   This identity lets the regulator set tier-specific adoption thresholds through the fixed charges in tariff (21).
--
--   **Formalization Note** The hypothesis $g_i>0$ makes the threshold division meaningful.
-- source:
--   Singh & Scheller-Wolf, That’s Not Fair: Tariff Structures for Electric Utilities with Rooftop Solar, SSRN 2926676 (SSRN Version), p. 18 (PDF 18), §4.3, paragraph before T*; p. S.3 (PDF 35), proof of Proposition 5(a)

import Mathlib
import Definitions.Def_SolarTariff_Fair_Model

namespace SolarTariff.Fair

theorem T3_threshold {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Market ι) (τ : T3 ι) (i : ι) (hg : 0 < M.g i) :
    threshold M (τ.bills M) i = τ.pr - τ.f i / M.g i := by sorry

end SolarTariff.Fair
