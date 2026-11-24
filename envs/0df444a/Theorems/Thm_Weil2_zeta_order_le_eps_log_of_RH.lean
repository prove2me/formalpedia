-- Prove2me | Theorems.Thm_Weil2_zeta_order_le_eps_log_of_RH
-- name    : Weil2.zeta_order_le_eps_log_of_RH
-- status  : Proved
-- author  : @xuanji
-- created : 2026-11-24T04:16:53.386827+00:00
-- url     : https://prove2.me/theorems/5006b48b-3d0b-42aa-b6f9-e43a021f5625
-- title:
--   Under RH, zeta zero multiplicities are $o(\log\gamma)$
-- statement:
--   Assume the Riemann hypothesis. For every $\eta>0$ there is $T_0$ such that every zero $\rho=\beta+i\gamma$ of the Riemann zeta function with $\gamma\ge T_0$ has multiplicity $m_\rho\le\eta\log\gamma$. In other words, under RH the multiplicity of a zero at height $\gamma$ is $o(\log\gamma)$ (a weak form of Littlewood's bound $m_\rho\ll\log\gamma/\log\log\gamma$). The multiplicity is the meromorphic order of $\zeta$ at $\rho$.
-- source:
--   Weak form of Littlewood's multiplicity bound under RH; Titchmarsh, The Theory of the Riemann Zeta-Function, 2nd ed., §14.13. Proof via the Hadamard product of xi.

import Mathlib

namespace Weil2

theorem zeta_order_le_eps_log_of_RH (hRH : RiemannHypothesis) :
    ∀ η : ℝ, 0 < η → ∃ T0 : ℝ, ∀ ρ : ℂ, riemannZeta ρ = 0 → T0 ≤ ρ.im →
      (((meromorphicOrderAt riemannZeta ρ).untopD 0 : ℤ) : ℝ) ≤ η * Real.log ρ.im := by sorry

end Weil2
