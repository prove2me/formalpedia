-- Prove2me | Theorems.Thm_SpreadBetting_Inertial_lemma_2
-- name    : SpreadBetting.Inertial.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T12:32:21.547982+00:00
-- url     : https://prove2.me/theorems/b175ec22-6272-480c-8cb7-546fc4335b51
-- title:
--   Lemma 2, p. 21 — J̄ⁱ is the expected continuation profit of the threshold strategy ξ*_i (4.10)
-- statement:
--   Let the market satisfy the standing assumptions and $\rho(z) = 1/(r_0 + rz)$ with $r \in (0, \bar r)$. Under hypothesis $H_i$, the inertial policy and the threshold strategy $\xi_i^*$ of (4.4), for all $z \in \mathbb Z$,
--   $$
--   \bar J^1(z) = \lim_{T\to\infty} \mathbb E_1^z\Big[\sum_{t=1}^T j_1^+(Z_t)\,\mathbb I\{Z_t < \bar z\}\Big],\qquad
--   \bar J^0(z) = \lim_{T\to\infty} \mathbb E_0^z\Big[\sum_{t=1}^T j_0^-(Z_t)\,\mathbb I\{Z_t > -\bar z\}\Big]. \tag{4.10}
--   $$
--   Here $\mathbb E_i^z$ is the expectation from $Z_1 = z$ and $j_i^\pm(z) := j_i^\pm(\tilde s(z))$.
--
--   So the closed form (4.8) is the total profit that the threshold strategy actually earns.
-- source:
--   Birge, Feng, Keskin & Schultz, SSRN 3283392 (version of April 14, 2020), p. 21, Lemma 2, (4.10); (4.4) p. 17; (4.8) p. 20

import Mathlib
import Definitions.Def_SpreadBetting_Inertial_Model

namespace SpreadBetting.Inertial

open MeasureTheory ProbabilityTheory Filter Topology

theorem lemma_2 (M : Market) (hM : M.Standing) (r : ℝ) (hr0 : 0 < r) (hr : r < rbar M) :
    let ρp := rhoIP M r
    (∀ z : ℤ, Tendsto (fun T : ℕ => cumExp M ρp 1 (xiStar M ρp 1)
        (fun z _ _ => jPlusZ M ρp 1 z * indic (belowZbar M ρp z)) T [] z) atTop
        (𝓝 (Jbar1 M ρp z))) ∧
    (∀ z : ℤ, Tendsto (fun T : ℕ => cumExp M ρp 0 (xiStar M ρp 0)
        (fun z _ _ => jMinusZ M ρp 0 z * indic (belowZbar M ρp (-z))) T [] z) atTop
        (𝓝 (Jbar0 M ρp z))) := by sorry

end SpreadBetting.Inertial
