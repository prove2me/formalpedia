-- Prove2me | Theorems.Thm_VerticalOwnership_CompleteInfo_vr_diag_concave_max
-- name    : VerticalOwnership.CompleteInfo.vr_diag_concave_max
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T06:40:42.248985+00:00
-- url     : https://prove2.me/theorems/668b694a-716d-4392-96de-880d738044da
-- title:
--   Appendix E, Proof of Theorem 1, p. 43 — v_r(q, q | μ_i) = r(q z_r(β) − ∫_ε̲^{q−μ_i} F) is concave, uniquely maximized at q* = μ_i + F⁻¹(z_r(β))
-- statement:
--   Let $\beta \in [0,1]$ and $\mu_i \in \{\mu_L, \mu_H\}$. When the retailer finances the entire capacity ($K = q^{adv} = q$):
--   1. for every $q$,
--   $$v_r(q, q \mid \mu_i) = r\Big(q\, z_r(\beta) - \int_{\underline{\varepsilon}}^{q-\mu_i} F(x)\,dx\Big);$$
--   2. $q \mapsto v_r(q, q \mid \mu_i)$ is concave;
--   3. it attains its maximum at $q^* = \mu_i + F^{-1}(z_r(\beta))$, and $q^*$ is the only maximizer;
--   4. the maximal value is
--   $$v_r(q^*, q^* \mid \mu_i) = r\Big(z_r(\beta)\big(\mu_i + F^{-1}(z_r(\beta))\big) - \int_{\underline{\varepsilon}}^{F^{-1}(z_r(\beta))} F(x)\,dx\Big).$$
--
--   This identifies the optimal advance order $q^*$ of (6) when the retailer finances the whole capacity.
--
--   **Formalization Note** The identity, concavity and maximization are stated over all real $q$; the paper's domain $q^{adv} \ge 0$ contains $q^*$ because $q^* > \mu_i + \underline\varepsilon \ge 0$. The paper's derivative computations are proof steps and are not posed.
-- source:
--   Avinadav, Shamir, Partial Vertical Ownership, Capacity Investment and Information Exchange in a Supply Chain, author manuscript of 2022-06-06 (Management Science, doi:10.1287/mnsc.2023.4673), p. 43, Appendix E, Proof of Theorem 1

import Mathlib
import Definitions.Def_VerticalOwnership_CompleteInfo_Setting
open MeasureTheory ProbabilityTheory

namespace VerticalOwnership.CompleteInfo

theorem vr_diag_concave_max (M : Model) (hM : M.Standing) (β : ℝ)
    (hβ : β ∈ Set.Icc (0 : ℝ) 1) (μ : ℝ) (hμ : μ ∈ ({M.μL, M.μH} : Set ℝ)) :
    (∀ q : ℝ, M.vr β μ q q = M.r * (q * M.zrβ β - ∫ x in M.εlo..q - μ, cdf M.P x)) ∧
      ConcaveOn ℝ Set.univ (fun q => M.vr β μ q q) ∧
      IsMaxOn (fun q => M.vr β μ q q) Set.univ (μ + M.Finv (M.zrβ β)) ∧
      (∀ q : ℝ, M.vr β μ q q = M.vr β μ (μ + M.Finv (M.zrβ β)) (μ + M.Finv (M.zrβ β)) →
        q = μ + M.Finv (M.zrβ β)) ∧
      M.vr β μ (μ + M.Finv (M.zrβ β)) (μ + M.Finv (M.zrβ β)) =
        M.r * (M.zrβ β * (μ + M.Finv (M.zrβ β)) - ∫ x in M.εlo..M.Finv (M.zrβ β), cdf M.P x) := by sorry

end VerticalOwnership.CompleteInfo
