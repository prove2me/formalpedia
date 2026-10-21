-- Prove2me | Theorems.Thm_SolarTariff_Fair_adoption_threshold
-- name    : SolarTariff.Fair.adoption_threshold
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:32:22.928573+00:00
-- url     : https://prove2.me/theorems/2373923f-1e1a-4030-b831-0a0cba70e3d6
-- title:
--   §4, pp. 12–13 — customer adoption threshold
-- statement:
--   Fix a customer tier $i$ with positive potential generation $g_i$, a tariff, and a solar price $p_s$. The tier weakly prefers adopting precisely when the solar price does not exceed its threshold:
--
--   $$T(d'_i,e_i,1)+p_sg_i\le T(d_i,0,0)\quad\Longleftrightarrow\quad p_s\le t(i)=\frac{T(d_i,0,0)-T(d'_i,e_i,1)}{g_i}.$$
--
--   Consequently, the induced adopter set contains $i$ exactly when adoption weakly minimizes that customer's cash outflow. Ties are settled in favor of adoption. This connects individual choice in (1) with the induced outcome used in P2.
--
--   **Formalization Note** The positivity of $g_i$ is an explicit denominator condition implicit in the printed formula.
-- source:
--   Singh & Scheller-Wolf, That’s Not Fair: Tariff Structures for Electric Utilities with Rooftop Solar, SSRN 2926676 (SSRN Version), pp. 12–13 (PDF 12–13), §4, paragraph after (6) and equation (8)

import Mathlib
import Definitions.Def_SolarTariff_Fair_Model

namespace SolarTariff.Fair

theorem adoption_threshold {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Market ι) (B : Bills ι) (i : ι) (ps : ℝ) (hg : 0 < M.g i) :
    (B.adopt i + ps * M.g i ≤ B.nonAdopt i ↔ ps ≤ threshold M B i) ∧
    (i ∈ adopters M B ps ↔ B.adopt i + ps * M.g i ≤ B.nonAdopt i) := by sorry

end SolarTariff.Fair
