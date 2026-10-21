-- Prove2me | Theorems.Thm_SubsetShrink_L1_fast_l1_step
-- name    : SubsetShrink.L1.fast_l1_step
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T21:26:37.941177+00:00
-- url     : https://prove2.me/theorems/01fae889-50ac-4193-8322-8e1c5652c2c0
-- title:
--   p. 43 — sparse ℓ1 difference bound for the fast rate
-- statement:
--   For $\lambda\ge0$ and two coefficient vectors $\beta,\hat\beta_1\in B_0(k)$,
--
--   $$\lambda\|\beta\|_1-\lambda\|\hat\beta_1\|_1\le\lambda\|\beta-\hat\beta_1\|_1\le\lambda\sqrt{2k}\,\|\beta-\hat\beta_1\|_2.$$
--
--   The support of their difference has at most $2k$ coordinates, connecting the penalty term to the sparse singular value in the fast rate.
-- source:
--   Mazumder, Radchenko & Dedieu, Subset Selection with Shrinkage, arXiv:1708.03288v4, p. 43, fast-rate paragraph, proof B.6

import Mathlib
import Definitions.Def_SubsetShrink_L1_Model

namespace SubsetShrink.L1

/-- The two ℓ1 steps in the fast-rate paragraph of B.6, p. 43. -/
theorem fast_l1_step {p : ℕ} (k : ℕ) (lam : ℝ)
    (βhat β : Fin p → ℝ) (hlam : 0 ≤ lam)
    (hβ : SubsetShrink.Events.l0 β ≤ k) (hhat : SubsetShrink.Events.l0 βhat ≤ k) :
    lam * SubsetShrink.Events.l1 β - lam * SubsetShrink.Events.l1 βhat ≤ lam * SubsetShrink.Events.l1 (β - βhat) ∧
    lam * SubsetShrink.Events.l1 (β - βhat) ≤
      lam * Real.sqrt (2 * (k : ℝ)) * SubsetShrink.Events.l2 (β - βhat) := by sorry

end SubsetShrink.L1
