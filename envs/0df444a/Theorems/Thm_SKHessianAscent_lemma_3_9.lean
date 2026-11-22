-- Prove2me | Theorems.Thm_SKHessianAscent_lemma_3_9
-- name    : SKHessianAscent.lemma_3_9
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-22T20:06:59.154882+00:00
-- url     : https://prove2.me/theorems/dabc68f5-b6db-493b-b714-63803e049173
-- title:
--   Lemma 3.9 — ASL-TAP and PHD are well posed up to the exit from the safe set and stay in the cube $(-1,1)^n$
-- statement:
--   Fix $0<\beta<1$, $c>0$ and a symmetric real $n\times n$ matrix $A$ with $\|A\|_{\mathrm{op}}\le3$; $D(m)=\mathrm{diag}(1/(1-m_i^2))$, $\widehat Q(m)=(\nabla^2_m\mathcal F_{\mathrm{TAP}}(m))^{-1}$, $f$ is the drift (2.4) and $\mathcal S_{\beta,A}(c)$ the safe set. Assume (d3), $\|f(m)-m\|_2\le\varepsilon_{\mathrm{drift}}$ on $\mathcal S_{\beta,A}(c)$, and $0_n\in\mathcal S_{\beta,A}(c)$. Let $W$ be a standard Brownian motion in $\mathbb R^n$ on a probability space. Then:
--
--   1. each of the primal equations (3.4) (ASL-TAP) and (3.5) (PHD), and each of the dual equations (d-ASL-TAP) and (d-PHD), has a strong solution up to its first exit from $\mathcal S_{\beta,A}(c)$, respectively from $\tanh^{-1}(\mathcal S_{\beta,A}(c))$, stopped there and defined for all $t\ge0$, and it is pathwise unique: two such solutions agree for all $t$ almost surely;
--   2. if $\widehat x$ solves a dual equation, then $\tanh(\widehat x)$ solves the corresponding primal equation;
--   3. almost surely, $\widehat m_{t\wedge\tau_c}\in(-1,1)^n$ for all $t<\infty$, for the stopped ASL-TAP and PHD processes;
--   4. on $\mathcal S_{\beta,A}(c)$ the integrand of the Jarzynski weight is bounded, $0\le\omega(m)\le\frac n2(c^{-1}+1)$, so the weight has a finite limit at a finite exit time and can be stopped there.
--
--   **Formalization Note** A solution up to the exit time is a continuous adapted process satisfying the stopped integral equation displayed in the proof of the lemma, with the published Itô integral; it is constant from its exit time on. The paper's last sentence ("the ASL tilt and JE weight also have finite limits at a finite exit") is rendered by the bound of item 4 on $\omega=\tfrac12(\mathrm{Tr}\,\widehat Q+\|m\|^2)$, which the proof derives from $\|\widehat m_s\|_2\le\sqrt n$ and $0\le\mathrm{Tr}\,\widehat Q(\widehat m_s)\le n/c$; the tilt $\widehat y_t=\int_0^t\widehat m_s\,ds+B_t$ has a bounded integrand for the same reason.
-- source:
--   H. Lee, J. S. Sandhu, J. Shi, Potential Hessian Ascent IV: Sampling the Sherrington–Kirkpatrick model at β < 1, https://arxiv.org/abs/2609.30590, §3.3, Lemma 3.9, pp. 14–15

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

theorem lemma_3_9 (β c ε : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) (hc : 0 < c) (n : ℕ)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsSymm) (hA3 : opNorm A ≤ 3)
    (hd3 : ∀ m ∈ safeSet β A c, l2 (fDrift β A m - m) ≤ ε)
    (h0 : (0 : Fin n → ℝ) ∈ safeSet β A c)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (W : ℝ≥0 → Ω → SDEState n) (hW : IsStandardBrownian P W) :
    ((∃ X, IsASLTAP P W β A c X) ∧
      ∀ X X', IsASLTAP P W β A c X → IsASLTAP P W β A c X' → ∀ᵐ ω ∂P, ∀ t, X t ω = X' t ω) ∧
    ((∃ X, IsPHD P W β A c X) ∧
      ∀ X X', IsPHD P W β A c X → IsPHD P W β A c X' → ∀ᵐ ω ∂P, ∀ t, X t ω = X' t ω) ∧
    ((∃ x, SolvesUntilExit P W (dualSafe β A c) (dualAslDrift β A) (dualSigma β A) x) ∧
      ∀ x x', SolvesUntilExit P W (dualSafe β A c) (dualAslDrift β A) (dualSigma β A) x →
        SolvesUntilExit P W (dualSafe β A c) (dualAslDrift β A) (dualSigma β A) x' →
        ∀ᵐ ω ∂P, ∀ t, x t ω = x' t ω) ∧
    ((∃ x, SolvesUntilExit P W (dualSafe β A c) (dualPhdDrift β A) (dualSigma β A) x) ∧
      ∀ x x', SolvesUntilExit P W (dualSafe β A c) (dualPhdDrift β A) (dualSigma β A) x →
        SolvesUntilExit P W (dualSafe β A c) (dualPhdDrift β A) (dualSigma β A) x' →
        ∀ᵐ ω ∂P, ∀ t, x t ω = x' t ω) ∧
    (∀ x, SolvesUntilExit P W (dualSafe β A c) (dualAslDrift β A) (dualSigma β A) x →
      IsASLTAP P W β A c fun t ω => tanhVec (x t ω)) ∧
    (∀ x, SolvesUntilExit P W (dualSafe β A c) (dualPhdDrift β A) (dualSigma β A) x →
      IsPHD P W β A c fun t ω => tanhVec (x t ω)) ∧
    (∀ X, IsASLTAP P W β A c X ∨ IsPHD P W β A c X → ∀ᵐ ω ∂P, ∀ t, X t ω ∈ cube n) ∧
    (∀ m ∈ safeSet β A c, 0 ≤ omega β A m ∧ omega β A m ≤ (n : ℝ) * (c⁻¹ + 1) / 2) := by sorry

end SKHessianAscent
