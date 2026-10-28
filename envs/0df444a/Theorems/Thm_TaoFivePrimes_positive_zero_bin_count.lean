-- Prove2me | Theorems.Thm_TaoFivePrimes_positive_zero_bin_count
-- name    : TaoFivePrimes.positive_zero_bin_count
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-27T21:47:58.053045+00:00
-- url     : https://prove2.me/theorems/bf03aef9-e96b-498f-b270-72231a7099af
-- title:
--   An explicit count for positive zeta zeros in a height interval
-- statement:
--   Let $Z$ be a finite set of distinct nontrivial zeros $\rho$ of the Riemann zeta function, with multiplicities $m_\rho$, and suppose $4\le L\le U$ and $L<\operatorname{Im}\rho\le U$ for every $\rho\in Z$. Then
--
--   $$
--   \sum_{\rho\in Z}m_\rho\le
--   \frac{U-L}{2\pi}\log\frac{U}{2\pi}+18\log(U+5)+158.
--   $$
--
--   The strict lower endpoint permits subtracting the zeros counted at $L$.
-- source:
--   Derived from the proved ExplicitPNT.DusartTable1 zero-count and reciprocal-weight modules, whose Dusart and supporting formalization references are recorded in their published sources.

import Definitions.Def_dusart_psi_433_20261014_PsiZeroSum
import Mathlib.Tactic
open DusartSmoothing

theorem TaoFivePrimes.positive_zero_bin_count (Z : Finset ℂ) (L U : ℝ) (hL : 4 ≤ L) (hLU : L ≤ U)
    (hZ : ∀ ρ ∈ Z, RvM.IsNontrivialZero ρ ∧ L < ρ.im ∧ ρ.im ≤ U) :
    (∑ ρ ∈ Z, (RvM.zeroMult ρ : ℝ)) ≤
      (U-L)/(2*Real.pi)*Real.log (U/(2*Real.pi)) + 18*Real.log (U+5) + 158 := by sorry
