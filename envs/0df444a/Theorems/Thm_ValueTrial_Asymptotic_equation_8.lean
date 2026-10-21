-- Prove2me | Theorems.Thm_ValueTrial_Asymptotic_equation_8
-- name    : ValueTrial.Asymptotic.equation_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T16:17:22.647587+00:00
-- url     : https://prove2.me/theorems/a0dea8d1-125c-437a-b585-180507b565d4
-- title:
--   Equation (8), p. 12 (PDF 14) — closed form of the expected net gain via the normal linear loss Ψ
-- statement:
--   Consider the value-based trial model under its standing assumptions, with an arbitrary setup cost $c_{cap}$ and post-adoption population $P(\cdot)$. Let $T>0$ and $r>0$, so that $Q=Tr/2>0$, and assume $P(T)\ge0$. Write $P_\rho(T)$ for the discounted post-adoption population, $\sigma_Z=\sigma_Z(Q)$, and let the indifference points be
--   $$
--   \alpha_N(T)=\frac{I_N}{(1-p_N)P_\rho(T)},\qquad \alpha_S(T)=\frac{I_S}{p_NP_\rho(T)} .
--   $$
--   Then the expected net gain (7) equals
--   $$
--   V(T,r)=-\big(c_{cap}(r)+c\tilde T_\rho(T)r\big)+\delta_{on}\frac{\tilde T_\rho(T)r}{2}(1-2p_N)\mu_0+e^{-\rho(T+\Delta)}P_\rho(T)\sigma_Z\Big[(1-p_N)\Psi\Big(\frac{\alpha_N(T)-\mu_0}{\sigma_Z}\Big)+p_N\Psi\Big(\frac{\alpha_S(T)+\mu_0}{\sigma_Z}\Big)\Big],
--   $$
--   where $\Psi(z)=\mathbb E[(Z-z)^+]$ is the standard normal linear loss.
--
--   This is the formula the paper's analysis works with: it turns the Gaussian expectation of the adoption payoff into two evaluations of $\Psi$.
--
--   **Formalization Note** The page sets $\alpha_S=\infty$ when $p_N=0$ or $P_\rho(T)=0$ and $\alpha_N=\infty$ when $P_\rho(T)=0$; Lean divides by zero to $0$ instead. The value is unaffected: $\alpha_S$ only appears multiplied by $p_N$, and when $P_\rho(T)=0$ both sides are $0$ (because $I_N,I_S\ge0$). The hypothesis $P(T)\ge0$ is the model's standing condition (Table EC.1). The statement asks for $T>0$ and $r>0$, the meaning of "$Tr>0$" on the decision box.
-- source:
--   Alban, Chick & Forster, Value-based clinical trials, accepted manuscript (Management Science 69(6), 2023; IRIS UniBo 11585/879132), p. 12 (PDF 14), eq. (8); αN, αS from pp. 11–12 (PDF 13–14)

import Mathlib
import Definitions.Def_ValueTrial_Asymptotic_Model

open MeasureTheory ProbabilityTheory Filter

namespace ValueTrial.Asymptotic

/-- Equation (8), p. 12 (PDF 14): when `Tr > 0`, the expected net gain (7) has the closed form
`-(ccap(r) + c T̃ρ(T) r) + δon (T̃ρ(T) r/2)(1 - 2pN) µ0
  + e^{-ρ(T+∆)} Pρ(T) σZ [(1 - pN) Ψ((αN(T) - µ0)/σZ) + pN Ψ((αS(T) + µ0)/σZ)]`,
with `αN(T) = IN/((1 - pN) Pρ(T))` and `αS(T) = IS/(pN Pρ(T))`. -/
theorem equation_8 (θ : Params) (hS : θ.Standing) (ccap Ppop : ℝ → ℝ) (T r : ℝ)
    (hT : 0 < T) (hr : 0 < r) (hP : 0 ≤ Ppop T) :
    let Pr := Prho θ (Ppop T)
    let sZ := sigZ θ (T * r / 2)
    let aN := θ.IN / ((1 - θ.pN) * Pr)
    let aS := θ.IS / (θ.pN * Pr)
    V θ ccap Ppop (T, r) =
      -(ccap r + θ.c * Ttil θ T * r) + θ.don * (Ttil θ T * r / 2) * (1 - 2 * θ.pN) * θ.mu0
        + Real.exp (-θ.rho * (T + θ.Del)) * Pr * sZ *
          ((1 - θ.pN) * InventoryControl.normalLoss ((aN - θ.mu0) / sZ)
            + θ.pN * InventoryControl.normalLoss ((aS + θ.mu0) / sZ)) := by sorry

end ValueTrial.Asymptotic
