-- Prove2me | Theorems.Thm_ShockWear_Inherit_Supplement_theorem32_11
-- name    : ShockWear.Inherit.Supplement.theorem32_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T23:52:13.333721+00:00
-- url     : https://prove2.me/theorems/b17c7156-31d6-4fd9-a960-9f26feee822d
-- title:
--   Theorem 3.2 (3.11) — Supermultiplicative shock survival gives NWU
-- statement:
--   Let $\lambda>0$ and $1\ge\bar P_0\ge\bar P_1\ge\cdots\ge0$. Suppose $\bar P_j\bar P_k\le\bar P_{j+k}$ for all nonnegative integers $j,k$. Then the Poisson shock survival $\bar H$ is new worse than used:
--
--   $$
--   \bar H(x)\bar H(t)\le\bar H(t+x)\qquad(x,t\ge0).
--   $$
--
--   This compares a new item's survival with conditional survival after use. Both zero ages and zero survival values remain in the cross-multiplied inequality.
--
--   **Formalization Note** The paper states the reversed NBU ratio inequality; we state its cross-product form, which agrees where the conditioning survival is positive and is trivial when it is zero.
--
--   Differences from the source:
--   - encoding: shock survival probabilities and Poisson rate → explicit λ>0, nonnegative antitone P with P₀≤1; reason: these are the probability assumptions in (1.1)–(2.2); P₀<1 retains the mass at the origin
--   - encoding: NWU survival ratios on defined denominators → cross-multiplied inequalities at all nonnegative ages; reason: zero survival is handled without a division-by-zero convention
--   - generalization: H is a proper life distribution, implicitly Pₖ→0 → the analytic class assertion also allows defective shock survivals; reason: bounded nonnegative coefficients still give convergent Poisson series and the same shape conclusion; every proper source law is included
-- source:
--   Esary, Marshall and Proschan, Shock Models and Wear Processes, Ann. Probability 1 (1973), p. 634, Theorem 3.2 (3.11); https://doi.org/10.1214/aop/1176996891

import Mathlib
import Definitions.Def_ShockWear_Inherit_Model
import Definitions.Def_ShockWear_Inherit_Supplement_ReversedAgeing

namespace ShockWear.Inherit.Supplement

open MeasureTheory
open scoped ENNReal

theorem theorem32_11 (lam : ℝ) (hlam : 0 < lam) (P : ℕ → ℝ)
    (hP0 : P 0 ≤ 1) (hanti : Antitone P) (hnn : ∀ k, 0 ≤ P k)
    (hprod : ∀ j k, P j * P k ≤ P (k + j)) :
    IsNWU (ShockWear.CumDamage.shockSurv lam P) := by sorry

end ShockWear.Inherit.Supplement
