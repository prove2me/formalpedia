-- Prove2me | Theorems.Thm_TaoFivePrimes_low_zero_reciprocal_weight_65000
-- name    : TaoFivePrimes.low_zero_reciprocal_weight_65000
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-27T21:48:05.141326+00:00
-- url     : https://prove2.me/theorems/f13cbf0e-da2d-4223-953f-67d5a67e7adc
-- title:
--   Reciprocal-ordinate weight of zeta zeros through height 65,000
-- statement:
--   Let $Z$ be any finite set of distinct nontrivial zeros $\rho$ of the Riemann zeta function, with multiplicities $m_\rho$, and suppose $|\operatorname{Im}\rho|\le65000$ for every $\rho\in Z$. Then
--
--   $$
--   \sum_{\rho\in Z}\frac{m_\rho}{|\operatorname{Im}\rho|}\le\frac{301}{10}.
--   $$
--
--   Both positive and negative ordinates are included, and zeros are counted with analytic multiplicity.
-- source:
--   Derived from the proved ExplicitPNT.DusartTable1 zero-count and reciprocal-weight modules, whose Dusart and supporting formalization references are recorded in their published sources.

import Definitions.Def_dusart_psi_433_20261014_PsiZeroSum
import Mathlib.Tactic
open DusartSmoothing

theorem TaoFivePrimes.low_zero_reciprocal_weight_65000 (Z : Finset ℂ)
    (hZ : ∀ ρ ∈ Z, RvM.IsNontrivialZero ρ)
    (hγ : ∀ ρ ∈ Z, |ρ.im| ≤ 65000) :
    (∑ ρ ∈ Z, (RvM.zeroMult ρ : ℝ) * (1 / |ρ.im|)) ≤ (301/10:ℝ) := by sorry
