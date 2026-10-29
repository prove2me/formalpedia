-- Prove2me | Theorems.Thm_PeskirShiryaev_SequentialTesting_theorem_21_2
-- name    : PeskirShiryaev.SequentialTesting.theorem_21_2
-- status  : Disproved
-- author  : @Shuze Chen
-- created : 2026-10-29T02:28:00.87723+00:00
-- url     : https://prove2.me/theorems/ac668212-5592-480c-8410-b41c3ec3a1f1
-- title:
--   Theorem 21.2 — finite-horizon Bayesian sequential testing (printed statement)
-- statement:
--   Consider the finite-horizon Bayesian test of the two fixed drift hypotheses for $X_u=\theta\mu u+\sigma W_u$, with prior $p\in[0,1]$, positive error losses $a,b$, and horizon $T>0$. Let $H(p)=\min\{ap,b(1-p)\}$, $c=b/(a+b)$, and let $g_0,g_1$ be the contact boundaries of the variational value. The infinite-horizon threshold pair satisfies its root equations, and $g$ lies in the continuous monotone class $A_*\le g_0<c<g_1\le B_*$ before $T$, with both endpoints $c$.
--
--   The theorem asserts that
--   $$\tau_* = \inf\{0\le u\le T:\Pi^p_u\notin(g_0(u),g_1(u))\}$$
--   is admissible and attains the posterior value. There is an admissible optimal binary decision whose values satisfy the printed cases: $d_*=1$ when the stopped posterior equals $g_1(\tau_*)$, or $d_*=0$ when it equals $g_0(\tau_*)$. Its Bayesian risk equals $V(0,p)$ and is no larger than that of any admissible bounded test.
--
--   With $M(p,u)=E_pH(\Pi^p_u)$ and $K(p,u,q)=P_p(\Pi^p_u\le q)$, the boundaries solve
--   $$M(g_i(t),T-t)=H(g_i(t))+\int_0^{T-t}[K(g_i(t),u,g_0(t+u))-K(g_i(t),u,g_1(t+u))]\,du,$$
--   for $i=0,1$ and $0\le t\le T$, and are the unique solution in the stated boundary class. The theorem also asserts the two Gaussian expectation formulas (21.2.47) and $K(g_i(t),u,g_j(t+u))=Q_{\mu/\sigma}(g_i(t),u,g_j(t+u))$ from (21.2.48), for both $i,j$ and all admissible elapsed times. If $a=b$, then $g_1=1-g_0$ on $[0,T]$.
--
--   This is the chapter's complete finite-horizon boundary characterization, including its explicit numerical kernels.
--
--   **Formalization Note** This faithful anchor intentionally retains the two documented printed defects: the equality-only decision graph does not cover immediate stopping outside the continuation interval (F1), and the signed transition formula fails for $\mu/\sigma<0$ (F2). Consequently the anchor is expected to be disproved. At zero elapsed time the otherwise singular transition expression is assigned its deterministic point-mass value; Gaussian integration uses the standard normal measure. The finite-horizon restriction is the setting of §21.2 despite the theorem's citation of the earlier unrestricted equations.
-- source:
--   Peskir and Shiryaev, Optimal Stopping and Free-Boundary Problems, Birkhäuser Verlag, 2006, DOI 10.1007/978-3-7643-7390-0, pp. 299–301 / PDF pp. 316–318, Theorem 21.2, Eqs. (21.2.44)–(21.2.48)

import Definitions.Def_PeskirShiryaev_SequentialTesting_BoundaryClass

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace PeskirShiryaev.SequentialTesting

/-- Theorem 21.2 as printed, (21.2.44)-(21.2.48). F1 and F2 are deliberately
retained: the two equality-only decision branches and the signed Gaussian
CDF coefficient. This anchor is expected to be false; see the separate variant. -/
theorem theorem_21_2 {Ω : Type*} [MeasurableSpace Ω]
    (P0 P1 : Measure Ω) [IsProbabilityMeasure P0] [IsProbabilityMeasure P1]
    (θ : Ω → Bool) (hθ : Measurable θ)
    (hθ0 : ∀ᵐ ω ∂P0, θ ω = false) (hθ1 : ∀ᵐ ω ∂P1, θ ω = true)
    (W : ℝ≥0 → Ω → ℝ) (hWmeas : ∀ u, Measurable (W u))
    (hWcont : ∀ ω, Continuous (fun u => W u ω)) (hW0 : ∀ ω, W 0 ω = 0)
    (hB0 : IsBrownianReal W P0) (hB1 : IsBrownianReal W P1)
    (μ σ a b T : ℝ) (hμ : μ ≠ 0) (hσ : σ ≠ 0)
    (ha : 0 < a) (hb : 0 < b) (hT : 0 < T) :
    let E : Model Ω :=
      { P0 := P0, P1 := P1, prob0 := inferInstance, prob1 := inferInstance,
        θ := θ, θ_measurable := hθ, θ_zero := hθ0, θ_one := hθ1,
        W := W, W_measurable := hWmeas, W_continuous := hWcont, W_zero := hW0,
        brownian0 := hB0, brownian1 := hB1 }
    let C : Parameters :=
      { μ := μ, σ := σ, a := a, b := b, T := T, drift_ne := hμ,
        noise_ne := hσ, a_pos := ha, b_pos := hb, horizon_pos := hT }
    let g := optimalBoundary E C
    ThresholdPair C (lowerThreshold C) (upperThreshold C) ∧
    BoundaryClass C g ∧ SolvesIntegralEquations E C g ∧
    (∀ h : Fin 2 → ℝ → ℝ, BoundaryClass C h →
      SolvesIntegralEquations E C h → ∀ i, EqOn (h i) (g i) (Icc 0 C.T)) ∧
    (∀ p ∈ Icc (0 : ℝ) 1,
      let τ := exitTime E C g 0 p
      Admissible E C C.T τ ∧ stoppingCost E C 0 p τ = value E C 0 p ∧
      ∃ d : Ω → Bool, AdmissibleDecision E C τ d ∧
        PrintedDecision E C g p τ d ∧ bayesRisk E C p τ d = value E C 0 p ∧
        ∀ (s : Ω → ℝ≥0) (e : Ω → Bool), Admissible E C C.T s →
          AdmissibleDecision E C s e → bayesRisk E C p τ d ≤ bayesRisk E C p s e) ∧
    (∀ t ∈ Icc (0 : ℝ) C.T, ∀ i : Fin 2,
      terminalMean E C (g i t) (C.T - t) = gaussianTerminalMean C (g i t) (C.T - t)) ∧
    (∀ t ∈ Icc (0 : ℝ) C.T, ∀ i j : Fin 2, ∀ u ∈ Icc (0 : ℝ) (C.T - t),
      transitionCDF E C (g i t) u (g j (t + u)) =
        gaussianTransitionCDF (C.μ / C.σ) (g i t) u (g j (t + u))) ∧
    (C.a = C.b → ∀ t ∈ Icc (0 : ℝ) C.T, g 1 t = 1 - g 0 t) := by sorry

end PeskirShiryaev.SequentialTesting
