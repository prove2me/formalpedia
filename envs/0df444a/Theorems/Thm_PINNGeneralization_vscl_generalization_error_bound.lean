-- Prove2me | Theorems.Thm_PINNGeneralization_vscl_generalization_error_bound
-- name    : PINNGeneralization.vscl_generalization_error_bound
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T05:48:39.389402+00:00
-- url     : https://prove2.me/theorems/9c394fd6-cc06-416c-bdff-d8214bd39489
-- title:
--   Theorem 4.1 (as proved): generalization error of PINNs for the viscous scalar conservation law
-- statement:
--   Assume the setting of eq. (4.18): $\nu>0$, $T>0$, $k\ge2$, $f,\bar u\in C^k$, $u\in C^k([0,1]\times[0,T])$ a classical solution of (4.1), and $u^*$ a neural network with a $C^\infty$ activation. Consider quadrature rules with $N_{tb}$ points in $(0,1)$, $N_{sb}$ points $t_n\in[0,T]$ (used at $x=0$ and at $x=1$), and $N_{int}$ points in $(0,1)\times(0,T)$, all with nonnegative weights. Assume they satisfy (3.9)-(3.11) on $(0,1)$, $(0,T)$ and $(0,1)\times(0,T)$ for functions of class $C^k$, $C^k$ and $C^{k-2}$, with constants $C^{tb}_{quad},C^{sb}_{quad},C^{int}_{quad}$ and rates $\alpha_{tb},\alpha_{sb},\alpha_{int}>0$. With the training-error components of (4.7), $\mathbf C$, $\mathbf C_b$, $\bar{\mathbf C}_b$ as in eq. (4.18), and $A=T+\mathbf CT^2e^{\mathbf CT}$,
--
--   $$\begin{aligned}\mathcal E_G^2\le{}&A\Big[(\mathcal E_T^{tb})^2+(\mathcal E_T^{int})^2+2\bar{\mathbf C}_b\big((\mathcal E_T^{sb,0})^2+(\mathcal E_T^{sb,1})^2\big)+2\nu\mathbf C_bT^{1/2}\big(\mathcal E_T^{sb,0}+\mathcal E_T^{sb,1}\big)\Big]\\&+A\Big[C^{tb}N_{tb}^{-\alpha_{tb}}+C^{int}N_{int}^{-\alpha_{int}}+2\bar{\mathbf C}_b(C^{sb,0}+C^{sb,1})N_{sb}^{-\alpha_{sb}}+2\nu\mathbf C_bT^{1/2}\big((C^{sb,0})^{1/2}+(C^{sb,1})^{1/2}\big)N_{sb}^{-\alpha_{sb}/2}\Big],\end{aligned}$$
--
--   where $C^{tb}=C^{tb}_{quad}(\|\mathcal R_{tb}^2\|_{C^k})$, $C^{int}=C^{int}_{quad}(\|\mathcal R_{int}^2\|_{C^{k-2}})$, $C^{sb,0}=C^{sb}_{quad}(\|\mathcal R_{sb,0}^2\|_{C^k})$ and $C^{sb,1}=C^{sb}_{quad}(\|\mathcal R_{sb,1}^2\|_{C^k})$; these $C^k$ norms are taken over $(0,1)$, $[0,1]\times[0,T]$, $[0,T]$ and $[0,T]$ respectively.
--
--   The constants blow up as $\nu\to0$ when $\|u_x\|_\infty$ does (Remark 4.3).
--
--   **Formalization Note** The paper prints $(C^{sb,0}+C^{sb,1})^{1/2}$ in the last term. Its proof bounds $\big((\mathcal E^{sb,0})^2+c_0\big)^{1/2}+\big((\mathcal E^{sb,1})^2+c_1\big)^{1/2}$, which gives $c_0^{1/2}+c_1^{1/2}$ and not $(c_0+c_1)^{1/2}$. For example, $\mathcal E^{sb,0}=\mathcal E^{sb,1}=0$ and $c_0=c_1=1$ give $2>\sqrt2$. This statement gives what the proof establishes. The constants $C_{f,u,u^*}$ and $\bar{\mathbf C}_b$ are those of eq. (4.18).
-- source:
--   Mishra and Molinaro, Estimates on the generalization error of Physics Informed Neural Networks (PINNs) for approximating PDEs, arXiv:2006.16144v3 (2023), Section 4.3, Theorem 4.1, eqs. (4.8)-(4.9), p. 21; quadrature assumptions (3.9)-(3.11), p. 13

import Mathlib
import Definitions.Def_PINNGeneralization_Basic

open MeasureTheory

namespace PINNGeneralization

theorem vscl_generalization_error_bound {k : ℕ} (hk : 2 ≤ k) (T ν : ℝ) (hT : 0 < T) (hν : 0 < ν)
    (f : ℝ → ℝ) (hf : ContDiff ℝ k f) (ubar : ℝ → ℝ) (hubar : ContDiff ℝ k ubar)
    (u : ℝ → ℝ → ℝ) (hu : ContDiff ℝ k (fun q : ℝ × ℝ => u q.1 q.2))
    (hsol : IsVSCLSolution T ν f ubar u)
    (σ : ℝ → ℝ) (hσ : ContDiff ℝ (⊤ : ℕ∞) σ) (ustar : ℝ → ℝ → ℝ) (hustar : IsPINN1D σ ustar)
    (Qtb : QuadRule ℝ) (hQtb : Qtb.IsOn (Set.Ioo 0 1)) (hNtb : 0 < Qtb.N)
    (Qsb : QuadRule ℝ) (hQsb : Qsb.IsOn (Set.Icc 0 T)) (hNsb : 0 < Qsb.N)
    (Qint : QuadRule (ℝ × ℝ)) (hQint : Qint.IsOn (Set.Ioo 0 1 ×ˢ Set.Ioo 0 T))
    (hNint : 0 < Qint.N)
    (Ctb Csb Cint : ℝ → ℝ) (atb asb aint : ℝ) (hatb : 0 < atb) (hasb : 0 < asb)
    (haint : 0 < aint)
    (hqtb : QuadErrorBound volume (Set.Ioo 0 1) {g : ℝ → ℝ | ContDiff ℝ k g}
      (ckNorm k (Set.Ioo 0 1)) Ctb atb Qtb)
    (hqsb : QuadErrorBound volume (Set.Ioo 0 T) {g : ℝ → ℝ | ContDiff ℝ k g}
      (ckNorm k (Set.Icc 0 T)) Csb asb Qsb)
    (hqint : QuadErrorBound volume (Set.Ioo 0 1 ×ˢ Set.Ioo 0 T)
      {g : ℝ × ℝ → ℝ | ContDiff ℝ (k - 2) g} (ckNorm (k - 2) (rect T)) Cint aint Qint) :
    genErrorL2 (Set.Ioo 0 1) T u ustar ^ 2 ≤
      (T + (1 + 2 * vsclCf T f u ustar) * T ^ 2 * Real.exp ((1 + 2 * vsclCf T f u ustar) * T)) *
        (quadL2 Qtb (vsclResTb ubar ustar) ^ 2 +
          quadL2 Qint (fun q => vsclResInt ν f ustar q.1 q.2) ^ 2 +
          2 * vsclCbarb T f ustar *
            (quadL2 Qsb (fun t => ustar 0 t) ^ 2 + quadL2 Qsb (fun t => ustar 1 t) ^ 2) +
          2 * ν * vsclCb T u ustar * Real.sqrt T *
            (quadL2 Qsb (fun t => ustar 0 t) + quadL2 Qsb (fun t => ustar 1 t))) +
      (T + (1 + 2 * vsclCf T f u ustar) * T ^ 2 * Real.exp ((1 + 2 * vsclCf T f u ustar) * T)) *
        (Ctb (ckNorm k (Set.Ioo 0 1) (fun x => vsclResTb ubar ustar x ^ 2)) *
            (Qtb.N : ℝ) ^ (-atb) +
          Cint (ckNorm (k - 2) (rect T) (fun q => vsclResInt ν f ustar q.1 q.2 ^ 2)) *
            (Qint.N : ℝ) ^ (-aint) +
          2 * vsclCbarb T f ustar *
            ((Csb (ckNorm k (Set.Icc 0 T) (fun t => ustar 0 t ^ 2)) +
              Csb (ckNorm k (Set.Icc 0 T) (fun t => ustar 1 t ^ 2))) * (Qsb.N : ℝ) ^ (-asb)) +
          2 * ν * vsclCb T u ustar * Real.sqrt T *
            ((Real.sqrt (Csb (ckNorm k (Set.Icc 0 T) (fun t => ustar 0 t ^ 2))) +
              Real.sqrt (Csb (ckNorm k (Set.Icc 0 T) (fun t => ustar 1 t ^ 2)))) *
                (Qsb.N : ℝ) ^ (-asb / 2))) := by sorry

end PINNGeneralization
