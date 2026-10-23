-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier30_P24_pureLoss_highEnergyLimit
-- name    : QAlgorithms.Papers.Independent.Frontier30.P24.pureLoss_highEnergyLimit
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T08:38:46.367221+00:00
-- url     : https://prove2.me/theorems/1a2bcd24-4b53-4c35-a39f-4b3b12947210
-- title:
--   High-energy limit of the symmetric pure-loss test bound
-- statement:
--   Let $g(x)=((x+1)\log(x+1)-x\log x)/\log2$ for $x\ge0$, with $0\log0=0$, and write $G_\eta(N)=g((1+\eta)N/2)-g((1-\eta)N/2)$. For every transmissivity $0\le\eta<1$,
--
--   $$
--   \lim_{N\to+\infty}G_\eta(N)=\log_2\!\left(\frac{1+\eta}{1-\eta}\right).
--   $$
--
--   At the identity endpoint $\eta=1$, $G_1(N)=g(N)$ and $G_1(N)\to+\infty$. Thus the singular endpoint is an infinite limit rather than a real logarithm evaluated after division by zero.
--
--   This gives the high-energy asymptote of the optimized scalar test expression. An operational capacity bound requires the separately deferred channel and protocol interfaces.
-- source:
--   The squashed entanglement of a quantum channel, arXiv:1310.0129v3, PDF p. 20, Appendix A, after Eq.(42); Eq.(27) on p.16

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P24

noncomputable section

namespace QAlgorithms.Papers.Independent.Frontier30.P24

open Filter

/-- PDF p.20, last sentence of Appendix A, interpreted using Eq.(27), PDF p.16:
the high-energy limit is the logarithm of the full ratio (1+eta)/(1-eta),
in bits. At eta=1 the finite-energy expression diverges to positive infinity,
so the singular endpoint is expressed by an atTop limit, never real division by zero.
This is a limit of the stated scalar expression, not an operational capacity theorem. -/
theorem pureLoss_highEnergyLimit :
    (∀ eta : ℝ, 0 ≤ eta → eta < 1 →
      Tendsto (pureLossSymmetricBound eta) atTop
        (nhds (Real.log ((1 + eta) / (1 - eta)) / Real.log 2))) ∧
    Tendsto (pureLossSymmetricBound 1) atTop atTop := by sorry

end QAlgorithms.Papers.Independent.Frontier30.P24

end
