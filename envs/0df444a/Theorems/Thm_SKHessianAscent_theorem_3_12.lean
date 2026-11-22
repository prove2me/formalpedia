-- Prove2me | Theorems.Thm_SKHessianAscent_theorem_3_12
-- name    : SKHessianAscent.theorem_3_12
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-22T20:08:26.723606+00:00
-- url     : https://prove2.me/theorems/27bb3110-1f9a-4493-bd3c-e60b0686f0dc
-- title:
--   Theorem 3.12 — $T_2$ transport inequality for the path law of an Itô diffusion with bounded Lipschitz diffusion and Lipschitz drift
-- statement:
--   Let $C,K,T>0$. Consider the global solution of $dX_t=b(X_t)\,dt+\sigma(X_t)\,dB_t$, $X_0=0$, on $[0,T]$. Suppose that $\|\sigma(x)\|_{\mathrm{op}}\le C$ for all $x\in\mathbb R^n$, that $b$ is $K$-Lipschitz in Euclidean norm, and that $\sigma$ is $K/\sqrt n$-Lipschitz in the normalized Schatten norm $\|\cdot\|_{L^2}=\|\cdot\|_F/\sqrt n$. Then its path law on $C^0([0,T],\mathbb R^n)$ with the uniform Euclidean distance satisfies $T_2$ with constant
--   $$3TC^2\exp\big(3T(T+4)K^2\big).$$
--
--   **Formalization Note** "The global solution" is any strong solution in the sense of the published `EthierKurtz.SolvesBrownianSDE`, for a standard Brownian motion on an arbitrary probability space; the conclusion is for the path law of every such solution.
-- source:
--   H. Lee, J. S. Sandhu, J. Shi, Potential Hessian Ascent IV: Sampling the Sherrington–Kirkpatrick model at β < 1, https://arxiv.org/abs/2609.30590, §3.4, Theorem 3.12, p. 15 (Üstünel, modification of Theorem 1; time-homogeneous case of [DLSS26a, Theorem 6.12])

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

theorem theorem_3_12 (n : ℕ) (C K T : ℝ) (hC : 0 < C) (hK : 0 < K) (hT : 0 < T)
    (b : SDEState n → SDEState n) (σ : SDEState n → SDEDiffusion n)
    (hσ : ∀ x, opNorm (Matrix.of fun i j => σ x (i, j)) ≤ C)
    (hb : ∀ x y, ‖b x - b y‖ ≤ K * ‖x - y‖)
    (hσL : ∀ x y, ‖σ x - σ y‖ / Real.sqrt n ≤ K / Real.sqrt n * ‖x - y‖)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (W X : ℝ≥0 → Ω → SDEState n) (hW : IsStandardBrownian P W)
    (hX : SolvesBrownianSDE P (fun p => σ p.2) (fun p => b p.2) W (fun _ => 0) X) :
    SatisfiesT 2 (3 * T * C ^ 2 * Real.exp (3 * T * (T + 4) * K ^ 2)) (pathLaw P T X) := by sorry

end SKHessianAscent
