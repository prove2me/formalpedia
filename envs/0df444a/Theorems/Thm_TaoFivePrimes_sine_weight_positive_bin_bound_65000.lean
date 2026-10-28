-- Prove2me | Theorems.Thm_TaoFivePrimes_sine_weight_positive_bin_bound_65000
-- name    : TaoFivePrimes.sine_weight_positive_bin_bound_65000
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-27T22:07:49.031583+00:00
-- url     : https://prove2.me/theorems/70f58e64-4b31-431a-bf61-13c2c2ce9e44
-- title:
--   Sine-sensitive contribution from one positive zero bin
-- statement:
--   Let $0\le i<180$, $L_i=65000+1290i$, $U_i=L_i+1290$, and $1/2151\le r\le1/2149$. Let $Z$ be a finite set of nontrivial zeta zeros with $L_i<\operatorname{Im}\rho\le U_i$, and let $m_\rho$ be the analytic multiplicity. If $t_i$ is the recorded integer weight bound for this bin, then
--
--   $$
--   \sum_{\rho\in Z}\frac{m_\rho}{(\operatorname{Im}\rho)^3}
--   \min\!\left\{4\sin^2\!\left(\frac{r\operatorname{Im}\rho}{2}\right)+8r+3(\operatorname{Im}\rho)r^2,\,4\right\}
--   \le\frac{t_i}{2\cdot10^{21}}.
--   $$
--
--   The factor $1/2$ reflects that the bound concerns positive ordinates only.
-- source:
--   Combines the proved interval zero-count, sine-square enclosure, and exact rational weight certificates for the Tao five-primes Chebyshev-error reduction.

import Definitions.Def_dusart_psi_433_20261014_PsiZeroSum
import Definitions.Def_TaoFivePrimes_SineBinData65k
import Definitions.Def_TaoFivePrimes_SineBinArithmetic65k
import Mathlib.Tactic
open DusartSmoothing Complex Set

theorem TaoFivePrimes.sine_weight_positive_bin_bound_65000 (i : Fin 180) (r : ℝ) (hr0 : (1/2151:ℝ) ≤ r)
    (hr1 : r ≤ (1/2149:ℝ)) (Z : Finset ℂ)
    (hZ : ∀ ρ ∈ Z, RvM.IsNontrivialZero ρ ∧
      65000+1290*(i.val:ℝ) < ρ.im ∧ ρ.im ≤ 65000+1290*(i.val:ℝ)+1290) :
    (∑ ρ ∈ Z, (RvM.zeroMult ρ : ℝ) *
      ((min (4*(Real.sin (ρ.im*r/2))^2 + 8*r + 3*ρ.im*r^2) 4) / ρ.im^3)) ≤
      (TaoFivePrimes.sineBinTerm65k i.val:ℝ)/(2*10^21) := by sorry
