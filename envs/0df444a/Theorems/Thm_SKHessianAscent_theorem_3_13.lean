-- Prove2me | Theorems.Thm_SKHessianAscent_theorem_3_13
-- name    : SKHessianAscent.theorem_3_13
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-22T20:09:06.538675+00:00
-- url     : https://prove2.me/theorems/9565a680-5e4e-46c6-af51-0e00bb61b122
-- title:
--   Theorem 3.13 — a globally Lipschitz extension of ASL-TAP: transport inequality and sub-Gaussian concentration of Lipschitz path functionals
-- statement:
--   For all $L,L_{\mathrm{drift}}>0$ there is a constant $K=K(L,L_{\mathrm{drift}})>0$ with the following property. Fix $0<\beta<1$, $c>0$ and a symmetric real $n\times n$ matrix $A$ with $\|A\|_{\mathrm{op}}\le3$; $D(m)=\mathrm{diag}(1/(1-m_i^2))$, $\widehat Q(m)=(\nabla^2_m\mathcal F_{\mathrm{TAP}}(m))^{-1}$, $f$ is the drift (2.4) and $\mathcal S_{\beta,A}(c)$ the safe set. Assume (d3), (d4) with constants $L$ (for $\widehat Q$ in Frobenius norm) and $L_{\mathrm{drift}}$ (for $m\mapsto\widehat Q(m)(m-f(m))$), and $0_n\in\mathcal S_{\beta,A}(c)$. Let $0<T<\infty$ and
--   $$c_{T_2}=3Tc^{-2}\exp\big(3T(T+4)K^2\big).\tag{3.7}$$
--   Then there are coefficients $b_{\mathrm{ext}}:\mathbb R^n\to\mathbb R^n$ and $\sigma_{\mathrm{ext}}:\mathbb R^n\to\mathbb R^{n\times n}$ that agree on $\mathcal S_{\beta,A}(c)$ with $\widehat Q(m)(m-f(m))$ and $\widehat Q(m)$, such that for every standard Brownian motion $B$:
--
--   - the equation $d\widehat m^{\mathrm{ext}}_t=b_{\mathrm{ext}}(\widehat m^{\mathrm{ext}}_t)\,dt+\sigma_{\mathrm{ext}}(\widehat m^{\mathrm{ext}}_t)\,dB_t$, $\widehat m^{\mathrm{ext}}_0=0$ (3.6), has a global strong solution;
--   - driven by the same Brownian motion, every such solution agrees with the original ASL-TAP process up to its first exit from $\mathcal S_{\beta,A}(c)$;
--   - (i) its path law $P$ on $C^0([0,T],\mathbb R^n)$ with the uniform norm satisfies $d_{W,2}(P,\mu)^2\le2c_{T_2}H(\mu\mid P)$ for every probability measure $\mu$;
--   - (ii) every $P$-integrable $K_F$-Lipschitz functional $F$ satisfies $\mathbf E_P[e^{\lambda(F-\mathbf E_P[F])}]\le\exp(\lambda^2c_{T_2}K_F^2/2)$ for all $\lambda\in\mathbb R$ (3.8), and $P\{|F-\mathbf E_P[F]|>r\}\le2\exp(-r^2/(2c_{T_2}K_F^2))$ for $r>0$.
--
--   **Formalization Note** "A constant $K$ depending on $L$ and $L_{\mathrm{drift}}$" is a constant chosen before $\beta$, $c$, $T$, $n$ and $A$. Global strong solutions are those of the published `EthierKurtz.SolvesBrownianSDE`.
-- source:
--   H. Lee, J. S. Sandhu, J. Shi, Potential Hessian Ascent IV: Sampling the Sherrington–Kirkpatrick model at β < 1, https://arxiv.org/abs/2609.30590, §3.4, Theorem 3.13 and (3.6)–(3.8), p. 16

import Mathlib
import Definitions.Def_EthierKurtz_SDEState
import Definitions.Def_EthierKurtz_SDEDiffusion
import Definitions.Def_EthierKurtz_IsStandardBrownian
import Definitions.Def_EthierKurtz_SolvesBrownianSDE
import Definitions.Def_SKWeakPoincare_PathSpace
import Definitions.Def_SKHessianAscent_Model
import Definitions.Def_SKHessianAscent_Transport
import Definitions.Def_SKHessianAscent_Dynamics

open MeasureTheory ProbabilityTheory Filter EthierKurtz
open scoped NNReal ENNReal Topology BigOperators

namespace SKHessianAscent

theorem theorem_3_13 (L Ld : ℝ) (hL : 0 < L) (hLd : 0 < Ld) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (β c ε T : ℝ) (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ),
        0 < β → β < 1 → 0 < c → 0 < T → A.IsSymm → opNorm A ≤ 3 →
        (∀ m ∈ safeSet β A c, l2 (fDrift β A m - m) ≤ ε) →
        (∀ m ∈ safeSet β A c, ∀ w ∈ safeSet β A c,
          frob (Qhat β A m - Qhat β A w) ≤ L * l2 (m - w)) →
        (∀ m ∈ safeSet β A c, ∀ w ∈ safeSet β A c,
          l2 (aslDrift β A m - aslDrift β A w) ≤ Ld * l2 (m - w)) →
        (0 : Fin n → ℝ) ∈ safeSet β A c →
        ∃ (bext : SDEState n → SDEState n) (σext : SDEState n → SDEDiffusion n),
          (∀ m ∈ safeSet β A c,
            bext (WithLp.toLp 2 m) = WithLp.toLp 2 (aslDrift β A m) ∧
            ∀ i j, σext (WithLp.toLp 2 m) (i, j) = Qhat β A m i j) ∧
          ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
            (W : ℝ≥0 → Ω → SDEState n), IsStandardBrownian P W →
            (∃ X, SolvesBrownianSDE P (fun p => σext p.2) (fun p => bext p.2) W (fun _ => 0) X) ∧
            ∀ X, SolvesBrownianSDE P (fun p => σext p.2) (fun p => bext p.2) W (fun _ => 0) X →
              (∀ M : ℝ≥0 → Ω → Fin n → ℝ, IsASLTAP P W β A c M →
                ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
                  (t : ℝ≥0∞) ≤ exitTime (safeSet β A c) (fun s => M s ω) →
                    ∀ i, X t ω i = M t ω i) ∧
              SatisfiesT 2 (3 * T * c ^ (-2 : ℤ) * Real.exp (3 * T * (T + 4) * K ^ 2))
                (pathLaw P T X) ∧
              ∀ (F : SKWeakPoincare.PathSpace T n → ℝ) (KF : ℝ≥0), LipschitzWith KF F →
                Integrable F (pathLaw P T X) →
                (∀ lam : ℝ,
                  ∫⁻ γ, ENNReal.ofReal
                      (Real.exp (lam * (F γ - ∫ γ', F γ' ∂(pathLaw P T X)))) ∂(pathLaw P T X) ≤
                    ENNReal.ofReal (Real.exp (lam ^ 2 *
                      (3 * T * c ^ (-2 : ℤ) * Real.exp (3 * T * (T + 4) * K ^ 2)) *
                      (KF : ℝ) ^ 2 / 2))) ∧
                (∀ r : ℝ, 0 < r →
                  pathLaw P T X {γ | r < |F γ - ∫ γ', F γ' ∂(pathLaw P T X)|} ≤
                    ENNReal.ofReal (2 * Real.exp (-r ^ 2 / (2 *
                      (3 * T * c ^ (-2 : ℤ) * Real.exp (3 * T * (T + 4) * K ^ 2)) *
                      (KF : ℝ) ^ 2)))) := by sorry

end SKHessianAscent
