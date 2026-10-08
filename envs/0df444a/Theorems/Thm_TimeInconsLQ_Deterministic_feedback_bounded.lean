-- Prove2me | Theorems.Thm_TimeInconsLQ_Deterministic_feedback_bounded
-- name    : TimeInconsLQ.Deterministic.feedback_bounded
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T13:27:08.580977+00:00
-- url     : https://prove2.me/theorems/396d688b-13d3-4b6a-9d8f-0dcf7ef62a4f
-- title:
--   Proof of Theorem 4.4, p. 14 — α is bounded and β square integrable, so u* ∈ L² and X* ∈ L²(Ω; C(0, T; ℝ))
-- statement:
--   Consider the scalar-state problem with deterministic coefficients of §4 under the standing assumptions, with $G\ge h>0$ and one of the cases (i), (ii), (iii) of Theorem 4.4. Let $(M,N)$ be a positive solution pair of (4.9) on $[0,T]$ and $\Phi$ a solution of (4.8), and let $\alpha,\beta$ be the feedback coefficients (4.4).
--
--   **Claim.** The following hold.
--   1. $\alpha$ is essentially bounded on $[0,T]$, and $\beta$ is square integrable on $[0,T]$.
--   2. On every probability space carrying a standard $d$-dimensional Brownian motion and for every initial state $x_0$, the closed-loop equation
--   $$dX^*_s=[A_sX^*_s+B_s'(\alpha_sX^*_s+\beta_s)+b_s]ds+[C_sX^*_s+D_s(\alpha_sX^*_s+\beta_s)+\sigma_s]'dW_s,\qquad X^*_0=x_0,$$
--   has a solution $X^*$ with continuous paths on $[0,T]$ and $\mathbb E\sup_{s\le T}|X^*_s|^2<\infty$ (that is, $X^*\in L^2_{\mathcal F}(\Omega;C(0,T;\mathbb R))$), whose feedback control $u^*=\alpha X^*+\beta$ lies in $L^2_{\mathcal F}(0,T;\mathbb R^l)$.
--
--   This is the integrability step of the proof of Theorem 4.4: the linear feedback is admissible and its state is well defined.
--
--   **Formalization Note.** The paper states that $\alpha$ and $\beta$ are "uniformly bounded". Under the paper's assumptions ($\sigma\in L^2$ only, $B,C,D$ essentially bounded) $\alpha$ is essentially bounded but $\beta$ is in general only square integrable, since it contains $M_sD_s'\sigma_s$; we state the true version, which suffices for the conclusion. "$X^*\in L^2(\Omega;C)$" is stated as existence of a solution with these properties, because the substrate's notion of SDE solution already contains $\sup_s\mathbb E|X_s|^2<\infty$ and $u^*\in L^2$ is not implied by it.
-- source:
--   Hu, Jin, Zhou, Time-Inconsistent Stochastic Linear–Quadratic Control, arXiv:1111.0818v1, p. 14, proof of Theorem 4.4

import Mathlib
import Definitions.Def_Peng1990_SMP_Stochastic
import Definitions.Def_TimeInconsLQ_Deterministic_Model
import Definitions.Def_TimeInconsLQ_Deterministic_Riccati
import Definitions.Def_TimeInconsLQ_Deterministic_Ansatz

open MeasureTheory ProbabilityTheory Filter Topology Matrix
open scoped ENNReal NNReal

namespace TimeInconsLQ.Deterministic

/-- Proof of Theorem 4.4 (p. 14): in each of the three cases, for a positive solution pair
`(M, N)` of (4.9) and a solution `Φ` of (4.8), the gain `α` of (4.4) is essentially bounded on
`[0, T]` and `β` is square integrable on `[0, T]` (bounded when `σ` is); hence, on every
probability space with a Brownian motion, the closed-loop equation has a solution `X*` with
continuous paths and `E sup_{s ≤ T}|X*_s|² < ∞`, whose feedback control is in `L²_𝓕(0, T; ℝˡ)`. -/
theorem feedback_bounded {Ω : Type*} [MeasurableSpace Ω] {l d : ℕ} (c : Coeffs l d)
    (T : ℝ≥0) (hT : 0 < T) (hc : CoeffsStanding c T) (hGh : c.h ≤ c.G) (hh : 0 < c.h)
    (hcase : Case_i c T ∨ Case_ii c T ∨ Case_iii c T)
    (M N Φ : ℝ≥0 → ℝ) (hMN : IsPosSol49 c T M N) (hΦ : IsSol48 c T M N Φ) :
    (∃ K : ℝ, ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      ‖alpha c T M N s.toNNReal‖ ≤ K) ∧
    ∫⁻ s in Set.Icc (0 : ℝ) T, ‖beta c M Φ s.toNNReal‖ₑ ^ 2 < ⊤ ∧
    ∀ (P : Measure Ω), IsProbabilityMeasure P →
    ∀ (W : ℝ≥0 → Ω → Fin d → ℝ) (hW : Peng1990.SMP.IsStdBrownian P W) (x₀ : Fin 1 → ℝ),
      ∃ X, IsClosedLoop (toData c P W hW T hT x₀)
          (fun s _ => alpha c T M N s) (fun s _ => beta c M Φ s) X ∧
        TimeInconsLQ.Sufficient.Admissible (toData c P W hW T hT x₀) (fbControl c T M N Φ X) ∧
        (∀ᵐ ω ∂P, ContinuousOn (fun s => X s ω 0) (Set.Iic T)) ∧
        ∫⁻ ω, (⨆ s ∈ Set.Iic T, ‖X s ω 0‖ₑ ^ 2) ∂P < ⊤ := by sorry

end TimeInconsLQ.Deterministic
