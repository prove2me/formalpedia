-- Prove2me | Theorems.Thm_TaoFivePrimes_positive_zero_bin_counts_65000
-- name    : TaoFivePrimes.positive_zero_bin_counts_65000
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-27T22:00:57.509815+00:00
-- url     : https://prove2.me/theorems/eca91205-2212-48bc-ad6e-104719041aec
-- title:
--   Multiplicity bounds for the 65,000-height zero bins
-- statement:
--   Let $i$ be an integer with $0\le i<15$, and let $Z$ be a finite set of nontrivial zeta zeros with $L<\operatorname{Im}\rho\le U$. Suppose $L\ge65000$, $U-L=1290$, and $U\le80480+15480i$. Let $c_{12i}$ be the corresponding stored multiplicity bound. Then
--
--   $$
--   \sum_{\rho\in Z}m_\rho\le c_{12i},
--   $$
--
--   where $m_\rho$ is the analytic multiplicity. In particular, this applies to each of the twelve width-$1290$ bins in the $i$th group.
-- source:
--   Derived from the proved ExplicitPNT.DusartTable1 zero-count and shifted zero-tail modules; supporting Dusart references are recorded in those published sources.

import Definitions.Def_dusart_psi_433_20261014_PsiZeroSum
import Definitions.Def_TaoFivePrimes_SineBinArithmetic65k
import Mathlib.Tactic
open DusartSmoothing

theorem TaoFivePrimes.positive_zero_bin_counts_65000 (i : Fin 15) (Z : Finset ℂ) (L U : ℝ)
    (hL : 65000 ≤ L) (hstep : U-L = 1290)
    (hU : U ≤ 80480+15480*(i.val:ℝ))
    (hZ : ∀ ρ ∈ Z, RvM.IsNontrivialZero ρ ∧ L < ρ.im ∧ ρ.im ≤ U) :
    (∑ ρ ∈ Z, (RvM.zeroMult ρ : ℝ)) ≤
      (TaoFivePrimes.sineBinCount65k (12*i.val):ℝ) := by sorry
