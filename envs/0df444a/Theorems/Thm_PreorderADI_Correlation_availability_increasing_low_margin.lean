-- Prove2me | Theorems.Thm_PreorderADI_Correlation_availability_increasing_low_margin
-- name    : PreorderADI.Correlation.availability_increasing_low_margin
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T14:51:22.148408+00:00
-- url     : https://prove2.me/theorems/fc610a6e-085e-43ad-94c6-ab050cf40e66
-- title:
--   LEMMA 1(i) — for c < v_L < 2c, z_L < 0 and the availability ξ is increasing in ρ
-- statement:
--   Fix the model parameters under the standing assumptions, and suppose the low-type margin is small:
--
--   $$
--   c < v_L < 2c.
--   $$
--
--   Then the critical-fractile quantile satisfies $z_L < 0$, and the consumers' belief of product availability $\xi(\rho) = \mathbb E\big[\Pr\big(\tilde X_L(X)/2 < Q(X)\big)\big]$ of (3) is strictly increasing in the demand correlation $\rho$ on $[0,1)$.
--
--   More accurate advance demand information (a larger $\rho$) therefore makes waiting more attractive to high-type consumers when the second-period margin is small, which pushes the preorder price down.
--
--   **Formalization Note** "Increasing" is read as strictly increasing (`StrictMonoOn` on $[0,1)$). The gloss "(i.e., $z_L < 0$)" is proved as part of the conclusion. The standing assumptions include the added $c > 0$, $\mu_H, \mu_L, \sigma_L > 0$.
-- source:
--   Li and Zhang, Advance demand information, price discrimination, and preorder strategies, Manufacturing Service Oper. Management 15(1), 2013, p. 62, §4.1, LEMMA 1(i)

import Mathlib
import Definitions.Def_PreorderADI_Correlation_Model

open MeasureTheory ProbabilityTheory

namespace PreorderADI.Correlation

theorem availability_increasing_low_margin (P : Params) (hP : P.Standing)
    (h2c : P.vL < 2 * P.c) :
    P.zL < 0 ∧ StrictMonoOn (availability P) (Set.Ico (0:ℝ) 1) := by sorry

end PreorderADI.Correlation
