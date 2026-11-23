-- Prove2me | Theorems.Thm_PINNConvergence_expected_loss_le_of_covering
-- name    : PINNConvergence.expected_loss_le_of_covering
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-23T20:06:54.678045+00:00
-- url     : https://prove2.me/theorems/88d43666-d647-4862-ae8c-dbe3b16808f7
-- title:
--   Lemma B.1: the expected PINN loss is bounded by a regularized empirical loss on covering samples
-- statement:
--   Assume Assumption 3.1 with $d\ge2$ and constants $c_r,C_r,c_b,C_b$. Let $0<\alpha\le1$ and $\lambda_r,\lambda_b\ge0$. Suppose $[\mathcal L[h]]_{\alpha;U}$, $[\mathcal B[h]]_{\alpha;\Gamma}$, $[f]_{\alpha;U}$ and $[g]_{\alpha;\Gamma}$ are finite. Let $x_r^1,\dots,x_r^{m_r}\in U$ and $x_b^1,\dots,x_b^{m_b}\in\Gamma$ ($m_r,m_b\ge1$) be such that every $x\in U$ lies within $\varepsilon_r>0$ of some $x_r^i$, and every $x\in\Gamma$ within $\varepsilon_b>0$ of some $x_b^j$. With $C_m=3\max\{C_rm_r\varepsilon_r^d,\,C_bm_b\varepsilon_b^{d-1}\}$,
--
--   $$\mathrm{Loss}^{PINN}(h;\lambda)\le C_m\Big[\mathrm{Loss}^{PINN}_m(h;\lambda)+\frac{3\lambda_r\varepsilon_r^{2\alpha}}{C_m}[\mathcal L[h]]^2_{\alpha;U}+\frac{3\lambda_b\varepsilon_b^{2\alpha}}{C_m}[\mathcal B[h]]^2_{\alpha;\Gamma}\Big]+3\lambda_r\varepsilon_r^{2\alpha}[f]^2_{\alpha;U}+3\lambda_b\varepsilon_b^{2\alpha}[g]^2_{\alpha;\Gamma}.$$
--
--   This is the deterministic half of Theorem 3.1. Lemma B.2 supplies the covering with high probability.
--
--   **Formalization Note** The operators $\mathcal L,\mathcal B$ are arbitrary maps on functions. Only the values $\mathcal L[h]$ and $\mathcal B[h]$ enter. The expected loss takes values in $[0,\infty]$ and is compared with the real right-hand side.
-- source:
--   Shin, Darbon and Karniadakis, On the convergence of physics informed neural networks for linear second-order elliptic and parabolic type PDEs, arXiv:2004.01806v2 (2020), Appendix B, Lemma B.1, eq. (B.1), p. 22

import Mathlib
import Definitions.Def_PINNConvergence_Basic

open MeasureTheory Filter Topology

namespace PINNConvergence

theorem expected_loss_le_of_covering {d : ℕ} (hd : 2 ≤ d) (U Gam : Set (Rd d))
    (μr μb : Measure (Rd d)) (cr Cr cb Cb : ℝ) (hA : DataDistAssumption U Gam μr μb cr Cr cb Cb)
    (α : ℝ) (hα : 0 < α ∧ α ≤ 1) (Lop Bop : (Rd d → ℝ) → Rd d → ℝ) (f g h : Rd d → ℝ)
    (lr lb : ℝ) (hl : 0 ≤ lr ∧ 0 ≤ lb)
    (hLh : holderConst α U (Lop h) < ⊤) (hBh : holderConst α Gam (Bop h) < ⊤)
    (hf : holderConst α U f < ⊤) (hg : holderConst α Gam g < ⊤)
    {mr mb : ℕ} (hmr : 1 ≤ mr) (hmb : 1 ≤ mb) (xr : Fin mr → Rd d) (xb : Fin mb → Rd d)
    (hxr : ∀ i, xr i ∈ U) (hxb : ∀ j, xb j ∈ Gam) (er eb : ℝ) (her : 0 < er) (heb : 0 < eb)
    (hcovr : ∀ x ∈ U, ∃ i, ‖x - xr i‖ ≤ er) (hcovb : ∀ x ∈ Gam, ∃ j, ‖x - xb j‖ ≤ eb) :
    let Cm := 3 * max (Cr * mr * er ^ d) (Cb * mb * eb ^ (d - 1))
    pinnLossExp Lop Bop f g lr lb μr μb h ≤
      ENNReal.ofReal (Cm * (pinnLossEmp Lop Bop f g lr lb xr xb h +
          3 * lr * er ^ (2 * α) / Cm * (holderConst α U (Lop h)).toReal ^ 2 +
          3 * lb * eb ^ (2 * α) / Cm * (holderConst α Gam (Bop h)).toReal ^ 2) +
        3 * lr * er ^ (2 * α) * (holderConst α U f).toReal ^ 2 +
        3 * lb * eb ^ (2 * α) * (holderConst α Gam g).toReal ^ 2) := by sorry

end PINNConvergence
