-- Prove2me | Theorems.Thm_TaoFivePrimes_sine_weight_tail_above_297200
-- name    : TaoFivePrimes.sine_weight_tail_above_297200
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-27T22:00:52.523864+00:00
-- url     : https://prove2.me/theorems/bf7da0c7-af43-408f-855c-7c55993c2c24
-- title:
--   Coarse zero-weight tail beyond the sine-bin range
-- statement:
--   Let $Z$ be a finite set of nontrivial zeta zeros satisfying $|\operatorname{Im}\rho|>297200$, with analytic multiplicities $m_\rho$. Then
--
--   $$
--   \sum_{\rho\in Z}\frac{4m_\rho}{|\operatorname{Im}\rho|^3}
--   \le\frac{81609874820}{10^{21}}.
--   $$
--
--   This is the tail allowance used after applying the coarse kernel bound beyond the 180 sine-sensitive bins.
-- source:
--   Derived from the proved ExplicitPNT.DusartTable1 zero-count and shifted zero-tail modules; supporting Dusart references are recorded in those published sources.

import Definitions.Def_dusart_psi_433_20261014_PsiZeroSum
import Definitions.Def_TaoFivePrimes_SineBinArithmetic65k
import Mathlib.Tactic
open DusartSmoothing

theorem TaoFivePrimes.sine_weight_tail_above_297200 (Z : Finset ℂ) (hZ : ∀ ρ ∈ Z, RvM.IsNontrivialZero ρ)
    (hγ : ∀ ρ ∈ Z, 297200 < |ρ.im|) :
    (∑ ρ ∈ Z, (RvM.zeroMult ρ : ℝ) * (4 / |ρ.im|^3)) ≤ (81609874820/10^21:ℝ) := by sorry
