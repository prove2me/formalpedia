-- Prove2me | Theorems.Thm_PINNGeneralization_heat_generalization_error_bound
-- name    : PINNGeneralization.heat_generalization_error_bound
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T05:47:41.144665+00:00
-- url     : https://prove2.me/theorems/f3884e9c-abca-44d8-a018-5af6606af02e
-- title:
--   Theorem 3.1 (as proved): generalization error of PINNs for the semilinear parabolic equation
-- statement:
--   Assume the setting of eq. (3.15): $D\subseteq\mathbb R^d$ open, connected and bounded with $C^k$ boundary, $k\ge2$, $T>0$, $f$ globally Lipschitz with constant $C_f$, $\bar u\in C^k$, $u\in C^k(\bar D\times[0,T])$ a classical solution of (3.1), and $u^*$ a neural network with a $C^\infty$ activation. Assume moreover $f\in C^{k-2}$. Consider quadrature rules with $N_{tb}$ points in $D$, $N_{sb}$ points in $\partial D\times[0,T]$ and $N_{int}$ points in $D\times(0,T)$, all with nonnegative weights, satisfying (3.9)-(3.11): for every $g$ of class $C^k$ (respectively $C^k$, $C^{k-2}$),
--
--   $$\Big|\int g-\sum_nw_ng(y_n)\Big|\le C_{quad}(\|g\|_{C^j})\,N^{-\alpha},$$
--
--   with the integral over $D$ (respectively over $\partial D\times[0,T]$ against $ds\,dt$, and over $D\times(0,T)$) and $\alpha_{tb},\alpha_{sb},\alpha_{int}>0$. With the training-error components $\mathcal E_T^{tb},\mathcal E_T^{sb},\mathcal E_T^{int}$ of (3.8),
--
--   $$\mathcal E_G\le C_1\Big(\mathcal E_T^{tb}+\mathcal E_T^{int}+C_2(\mathcal E_T^{sb})^{1/2}+(C^{tb}_{quad})^{1/2}N_{tb}^{-\alpha_{tb}/2}+(C^{int}_{quad})^{1/2}N_{int}^{-\alpha_{int}/2}+C_2(C^{sb}_{quad})^{1/4}N_{sb}^{-\alpha_{sb}/4}\Big),$$
--
--   where $C_1=\sqrt{T+(1+2C_f)T^2e^{(1+2C_f)T}}$, $C_2=\sqrt{2\,C_{\partial D}(u,u^*)\,T^{1/2}}$, $C^{tb}_{quad}=C^{tb}_{quad}(\|\mathcal R_{tb}^2\|_{C^k})$, $C^{sb}_{quad}=C^{sb}_{quad}(\|\mathcal R_{sb}^2\|_{C^k})$ and $C^{int}_{quad}=C^{int}_{quad}(\|\mathcal R_{int}^2\|_{C^{k-2}})$.
--
--   The bound shows that the boundary residual enters with a square root, and so carries more weight than the interior and initial residuals.
--
--   **Formalization Note** The paper prints $C_2=\sqrt{C_{\partial D}T^{1/2}}$. The proof establishes $C_2=\sqrt{2C_{\partial D}T^{1/2}}$ (see eq. (3.15)). The hypothesis $f\in C^{k-2}$ is added because the paper uses $\mathcal R_{int}\in C^{k-2}$ to apply (3.11), and this fails for a merely Lipschitz $f$. The exponent $\ell$ in (3.11) is taken to be $k-2$, as the theorem's constant requires. $C^k$ norms on sets are computed from derivatives of functions defined on the whole space. The hyperparameter $\lambda$ of the loss does not appear in the bound and is omitted.
-- source:
--   Mishra and Molinaro, Estimates on the generalization error of Physics Informed Neural Networks (PINNs) for approximating PDEs, arXiv:2006.16144v3 (2023), Section 3.3, Theorem 3.1, eqs. (3.12)-(3.13), p. 13; quadrature assumptions (3.9)-(3.11), p. 13

import Mathlib
import Definitions.Def_PINNGeneralization_Basic

open MeasureTheory

namespace PINNGeneralization

theorem heat_generalization_error_bound {n k : ℕ} (hk : 2 ≤ k) (D : Set (Pt (n + 1)))
    (hD : IsCkDomain k D) (T : ℝ) (hT : 0 < T) (f : ℝ → ℝ) (Cf : ℝ)
    (hf : ∀ v w, |f v - f w| ≤ Cf * |v - w|) (hfk : ContDiff ℝ (k - 2) f)
    (ubar : Pt (n + 1) → ℝ) (hubar : ContDiff ℝ k ubar)
    (u : Pt (n + 1) → ℝ → ℝ) (hu : ContDiff ℝ k (fun q : Pt (n + 1) × ℝ => u q.1 q.2))
    (hsol : IsHeatSolution D T f ubar u)
    (σ : ℝ → ℝ) (hσ : ContDiff ℝ (⊤ : ℕ∞) σ)
    (ustar : Pt (n + 1) → ℝ → ℝ) (hustar : IsPINN σ ustar)
    (Qtb : QuadRule (Pt (n + 1))) (hQtb : Qtb.IsOn D) (hNtb : 0 < Qtb.N)
    (Qsb : QuadRule (Pt (n + 1) × ℝ)) (hQsb : Qsb.IsOn (frontier D ×ˢ Set.Icc 0 T))
    (hNsb : 0 < Qsb.N)
    (Qint : QuadRule (Pt (n + 1) × ℝ)) (hQint : Qint.IsOn (D ×ˢ Set.Ioo 0 T))
    (hNint : 0 < Qint.N)
    (Ctb Csb Cint : ℝ → ℝ) (atb asb aint : ℝ) (hatb : 0 < atb) (hasb : 0 < asb)
    (haint : 0 < aint)
    (hqtb : QuadErrorBound volume D {g : Pt (n + 1) → ℝ | ContDiff ℝ k g} (ckNorm k D) Ctb atb Qtb)
    (hqsb : QuadErrorBound (bdryTimeMeasure D T) Set.univ
      {g : Pt (n + 1) × ℝ → ℝ | ContDiff ℝ k g} (ckNorm k (frontier D ×ˢ Set.Icc 0 T)) Csb asb Qsb)
    (hqint : QuadErrorBound volume (D ×ˢ Set.Ioo 0 T)
      {g : Pt (n + 1) × ℝ → ℝ | ContDiff ℝ (k - 2) g} (ckNorm (k - 2) (D ×ˢ Set.Ioo 0 T))
      Cint aint Qint) :
    genErrorL2 D T u ustar ≤
      heatC1 T Cf *
        (quadL2 Qtb (heatResTb ubar ustar) + quadL2 Qint (fun q => heatResInt f ustar q.1 q.2) +
          Real.sqrt (2 * heatCbdry D T u ustar * Real.sqrt T) *
            Real.sqrt (quadL2 Qsb (fun q => ustar q.1 q.2)) +
          Real.sqrt (Ctb (ckNorm k D (fun x => heatResTb ubar ustar x ^ 2))) *
            (Qtb.N : ℝ) ^ (-atb / 2) +
          Real.sqrt (Cint (ckNorm (k - 2) (D ×ˢ Set.Ioo 0 T)
            (fun q => heatResInt f ustar q.1 q.2 ^ 2))) * (Qint.N : ℝ) ^ (-aint / 2) +
          Real.sqrt (2 * heatCbdry D T u ustar * Real.sqrt T) *
            Csb (ckNorm k (frontier D ×ˢ Set.Icc 0 T) (fun q => ustar q.1 q.2 ^ 2)) ^ (1 / 4 : ℝ) *
              (Qsb.N : ℝ) ^ (-asb / 4)) := by sorry

end PINNGeneralization
