-- Prove2me | Theorems.Thm_PINNConvergence_residuals_converge_uniformly
-- name    : PINNConvergence.residuals_converge_uniformly
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-23T20:08:28.688568+00:00
-- url     : https://prove2.me/theorems/0593ad52-1c55-4819-9009-9acfc08c9703
-- title:
--   Theorem 3.2 (as proved): the residuals of Hölder-regularized minimizers converge uniformly
-- statement:
--   Suppose Assumptions 3.1 ($d\ge2$) and 3.2 hold, with fixed weights $\lambda_r,\lambda_b>0$ and smooth activation. For $m_r=m\ge1$ let $m_b=m_b(m)\ge1$ satisfy
--
--   $$m=O\big(m_b^{d/(d-1)}\big)\quad\text{and}\quad m_b^{d/(d-1)}=O(m),$$
--
--   and let $\lambda^R_m$ satisfy (3.2). For each $m$ draw $m$ iid samples from $\mu_r$ and, independently, $m_b(m)$ iid samples from $\mu_b$; the coupling between different $m$ is arbitrary. Let $h_m\in\mathcal H_m$ be a minimizer over $\mathcal H_m$ of the Hölder regularized loss $\mathrm{Loss}_m(\cdot;\lambda,\lambda^R_m)$ of (3.3). Then with probability $1$,
--
--   $$\lim_{m\to\infty}\mathcal L[h_m]=f\ \text{ in }C^0(U),\qquad\lim_{m\to\infty}\mathcal B[h_m]=g\ \text{ in }C^0(\Gamma).$$
--
--   **Formalization Note** This is the theorem as its proof establishes it. The paper assumes only $m_r=O(m_b^{d/(d-1)})$. The proof also uses $\max_j(\lambda^R_m)_j/\min_j(\lambda^R_m)_j=O(1)$, which needs the reverse bound $m_b^{d/(d-1)}=O(m_r)$. Without it the bound on $[\mathcal B[h_m]]_{\alpha;\Gamma}$, and hence the equicontinuity used for the boundary limit, is not established. The positivity $\lambda_r,\lambda_b>0$ is implicit in the paper: with $\lambda_r=0$ the loss does not see $f$. The first item of the theorem, a bound $\mathrm{Loss}^{PINN}(h_m)=O(m_r^{-\alpha/d})$ holding with a probability that depends on $m$, is not included. The classes $\mathcal H_m$ may depend on the samples (Remark 2.2). "Sufficiently smooth activation" is taken as $\sigma\in C^\infty$. The order $k$ is a free parameter and $\mathcal L,\mathcal B$ are arbitrary maps on functions: the statement does not tie $k$ to the order of a PDE, so it is more general than the paper's, and the proof does not use linearity.
-- source:
--   Shin, Darbon and Karniadakis, On the convergence of physics informed neural networks for linear second-order elliptic and parabolic type PDEs, arXiv:2004.01806v2 (2020), Section 3.1, Theorem 3.2 (second item, eq. (3.5)), pp. 11-12; proof in Appendix C, pp. 24-25

import Mathlib
import Definitions.Def_PINNConvergence_Basic

open MeasureTheory Filter Topology

namespace PINNConvergence

theorem residuals_converge_uniformly {d : ℕ} (hd : 2 ≤ d) (U Gam : Set (Rd d))
    (μr μb : Measure (Rd d)) (cr Cr cb Cb : ℝ) (hA1 : DataDistAssumption U Gam μr μb cr Cr cb Cb)
    (α : ℝ) (k : ℕ) (Lop Bop : (Rd d → ℝ) → Rd d → ℝ) (f g : Rd d → ℝ)
    (lr lb : ℝ) (hl : 0 < lr ∧ 0 < lb) (mb : ℕ → ℕ) (hmb : ∀ m, 1 ≤ mb m)
    (hrate : ∃ K : ℝ, ∀ m : ℕ, 1 ≤ m → (m : ℝ) ≤ K * (mb m : ℝ) ^ ((d : ℝ) / ((d : ℝ) - 1)))
    (hrate' : ∃ K : ℝ, ∀ m : ℕ, 1 ≤ m → (mb m : ℝ) ^ ((d : ℝ) / ((d : ℝ) - 1)) ≤ K * m)
    (lrR lbR : ℕ → ℝ) (hR : RegWeightCondition d α lr lb cr Cr cb Cb mb lrR lbR)
    {Smp : Type*} [MeasurableSpace Smp] (P : Measure Smp) [IsProbabilityMeasure P]
    (XR : ∀ m : ℕ, Smp → Fin m → Rd d) (XB : ∀ m : ℕ, Smp → Fin (mb m) → Rd d)
    (hX : IsIIDSampling P μr μb mb XR XB)
    (σ : ℝ → ℝ) (hσ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) σ) (H : ℕ → Smp → Set (Rd d → ℝ))
    (hA2 : NetClassAssumption σ k α U Gam Lop Bop f g lr lb mb XR XB H)
    (h : ℕ → Smp → Rd d → ℝ)
    (hmin : ∀ m : ℕ, 1 ≤ m → ∀ ω, h m ω ∈ H m ω ∧ ∀ h' ∈ H m ω,
      holderRegLoss α U Gam Lop Bop f g lr lb (lrR m) (lbR m) (XR m ω) (XB m ω) (h m ω) ≤
        holderRegLoss α U Gam Lop Bop f g lr lb (lrR m) (lbR m) (XR m ω) (XB m ω) h') :
    ∀ᵐ ω ∂P, TendstoUniformlyOn (fun m => Lop (h m ω)) f atTop U ∧
      TendstoUniformlyOn (fun m => Bop (h m ω)) g atTop Gam := by sorry

end PINNConvergence
