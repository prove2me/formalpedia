-- Prove2me | Theorems.Thm_SolarTariff_Fair_lemma_1
-- name    : SolarTariff.Fair.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:32:25.009664+00:00
-- url     : https://prove2.me/theorems/1ab601dc-c196-49b6-9017-afa184f907a0
-- title:
--   Lemma 1, p. S.3 — adopting tier's nonnegative tariff margin
-- statement:
--   Under tariff (21), let tier $i$ have positive potential generation $g_i$ and adopt at solar price $p_s$; equivalently, $p_s\le t(i)$. Then
--
--   $$g_i p_r-g_i p_s-f_i\ge0.$$
--
--   The inequality bounds the adopter's payment change and is used to establish the customer equity part of Proposition 5.
--
--   **Formalization Note** The explicit $g_i>0$ condition supports the paper's division by $g_i$ in $t(i)$.
-- source:
--   Singh & Scheller-Wolf, That’s Not Fair: Tariff Structures for Electric Utilities with Rooftop Solar, SSRN 2926676 (SSRN Version), p. S.3 (PDF 35), Lemma 1

import Mathlib
import Definitions.Def_SolarTariff_Fair_Model

namespace SolarTariff.Fair

theorem lemma_1 {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Market ι) (τ : T3 ι) (i : ι) (ps : ℝ)
    (hg : 0 < M.g i) (hi : ps ≤ threshold M (τ.bills M) i) :
    0 ≤ M.g i * τ.pr - M.g i * ps - τ.f i := by sorry

end SolarTariff.Fair
