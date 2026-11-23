-- Prove2me | Theorems.Thm_PINNConvergence_expected_pinn_loss_bound
-- name    : PINNConvergence.expected_pinn_loss_bound
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-23T20:07:48.1428+00:00
-- url     : https://prove2.me/theorems/9754f170-1f89-438b-a7c9-429a02a8974e
-- title:
--   Theorem 3.1: bound on the expected PINN loss ($d \ge 2$)
-- statement:
--   Suppose Assumption 3.1 holds with $d\ge2$. Let $0<\alpha\le1$, let $\lambda=(\lambda_r,\lambda_b)\ge0$ be fixed, and let $[f]_{\alpha;U},[g]_{\alpha;\Gamma}<\infty$. There is a constant $C'$, depending only on $\lambda,d,c_r,c_b,\alpha,f,g$, with the following property. Let $h$ and real numbers $R_r(h)$, $R_b(h)$ satisfy $[\mathcal L[h]]^2_{\alpha;U}\le R_r(h)$ and $[\mathcal B[h]]^2_{\alpha;\Gamma}\le R_b(h)$, and let $m_r,m_b\ge1$. Draw $m_r$ iid samples from $\mu_r$ and, independently, $m_b$ iid samples from $\mu_b$. Then with probability at least
--
--   $$\Big(1-\sqrt{m_r}\big(1-1/\sqrt{m_r}\big)^{m_r}\Big)\Big(1-\sqrt{m_b}\big(1-1/\sqrt{m_b}\big)^{m_b}\Big)$$
--
--   the following inequality holds:
--
--   $$\mathrm{Loss}^{PINN}(h;\lambda)\le C_m\,\mathrm{Loss}_m(h;\lambda,\hat\lambda^R_m)+C'\big(m_r^{-\alpha/d}+m_b^{-\alpha/(d-1)}\big).$$
--
--   Here $\mathrm{Loss}_m(h;\lambda,\hat\lambda^R_m)=\mathrm{Loss}^{PINN}_m(h;\lambda)+\hat\lambda^R_{r,m}R_r(h)+\hat\lambda^R_{b,m}R_b(h)$, and $C_m$ and $\hat\lambda^R_m$ are the constants of eq. (3.1).
--
--   Minimizing the regularized empirical loss therefore minimizes an upper bound on the expected PINN loss.
--
--   **Formalization Note** "Depending only on $\lambda,d,c_r,c_b,\alpha,f,g$" is encoded by the order of quantifiers. $C'$ is chosen after $U,\Gamma,\alpha,\lambda,c_r,c_b,f,g$ and before $\mu_r,\mu_b,C_r,C_b,\mathcal L,\mathcal B,h,R_r,R_b,m_r,m_b$. Because the Hölder constants take values in $[0,\infty]$, the paper's real inequality $[\mathcal L[h]]^2_{\alpha;U}\le R_r(h)$ is written together with $R_r(h),R_b(h)\ge0$, which it implies. The case $d=1$ of the theorem is not included.
-- source:
--   Shin, Darbon and Karniadakis, On the convergence of physics informed neural networks for linear second-order elliptic and parabolic type PDEs, arXiv:2004.01806v2 (2020), Section 3, Theorem 3.1 (case d >= 2), eq. (3.1), pp. 9-10; proof in Appendix B, p. 24

import Mathlib
import Definitions.Def_PINNConvergence_Basic

open MeasureTheory Filter Topology

namespace PINNConvergence

theorem expected_pinn_loss_bound {d : ℕ} (hd : 2 ≤ d) (U Gam : Set (Rd d)) (α : ℝ)
    (hα : 0 < α ∧ α ≤ 1) (lr lb : ℝ) (hl : 0 ≤ lr ∧ 0 ≤ lb) (cr cb : ℝ) (f g : Rd d → ℝ)
    (hf : holderConst α U f < ⊤) (hg : holderConst α Gam g < ⊤) :
    ∃ C' : ℝ, ∀ (μr μb : Measure (Rd d)) (Cr Cb : ℝ), DataDistAssumption U Gam μr μb cr Cr cb Cb →
      ∀ (Lop Bop : (Rd d → ℝ) → Rd d → ℝ) (h : Rd d → ℝ) (Rr Rb : ℝ), 0 ≤ Rr → 0 ≤ Rb →
        holderConst α U (Lop h) ^ 2 ≤ ENNReal.ofReal Rr →
        holderConst α Gam (Bop h) ^ 2 ≤ ENNReal.ofReal Rb →
        ∀ mr mb : ℕ, 1 ≤ mr → 1 ≤ mb →
          ENNReal.ofReal ((1 - Real.sqrt mr * (1 - 1 / Real.sqrt mr) ^ mr) *
              (1 - Real.sqrt mb * (1 - 1 / Real.sqrt mb) ^ mb)) ≤
            ((Measure.pi fun _ : Fin mr => μr).prod (Measure.pi fun _ : Fin mb => μb))
              {p | pinnLossExp Lop Bop f g lr lb μr μb h ≤
                ENNReal.ofReal (constCm d cr Cr cb Cb mr mb *
                    lossEmp Lop Bop f g lr lb (lamHatR d α lr cr Cr cb Cb mr mb)
                      (lamHatB d α lb cr Cr cb Cb mr mb) Rr Rb p.1 p.2 h +
                  C' * ((mr : ℝ) ^ (-α / d) + (mb : ℝ) ^ (-α / ((d : ℝ) - 1))))} := by sorry

end PINNConvergence
