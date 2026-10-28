-- Prove2me | Theorems.Thm_TaoFivePrimes_high_zero_reciprocal_cube_weight_65000
-- name    : TaoFivePrimes.high_zero_reciprocal_cube_weight_65000
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-27T21:50:27.121331+00:00
-- url     : https://prove2.me/theorems/33cf3846-c885-4eeb-87cf-1594caeb3c68
-- title:
--   Reciprocal-cube weight of zeta zeros above height 65,000
-- statement:
--   Let $Z$ be any finite set of distinct nontrivial zeros $\rho$ of the Riemann zeta function, with multiplicities $m_\rho$, and suppose $65000<|\operatorname{Im}\rho|$ for every $\rho\in Z$. Then
--
--   $$
--   \sum_{\rho\in Z}\frac{m_\rho}{|\operatorname{Im}\rho|^3}\le\frac{372}{10^{12}}.
--   $$
--
--   Both positive and negative ordinates are included, and zeros are counted with analytic multiplicity.
-- source:
--   Derived from the proved ExplicitPNT.DusartTable1 zero-count and reciprocal-weight modules, whose Dusart and supporting formalization references are recorded in their published sources.

import Definitions.Def_dusart_psi_433_20261014_PsiZeroSum
import Mathlib.Tactic
open DusartSmoothing

theorem TaoFivePrimes.high_zero_reciprocal_cube_weight_65000 (Z : Finset ℂ)
    (hZ : ∀ ρ ∈ Z, RvM.IsNontrivialZero ρ)
    (hγ : ∀ ρ ∈ Z, 65000 < |ρ.im|) :
    (∑ ρ ∈ Z, (RvM.zeroMult ρ : ℝ) * (1 / |ρ.im|^3)) ≤ (372/10^12:ℝ) := by sorry
