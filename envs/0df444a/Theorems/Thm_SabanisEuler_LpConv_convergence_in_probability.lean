-- Prove2me | Theorems.Thm_SabanisEuler_LpConv_convergence_in_probability
-- name    : SabanisEuler.LpConv.convergence_in_probability
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-29T00:26:33.027998+00:00
-- url     : https://prove2.me/theorems/b19042c2-49c2-46b4-94e8-085fd9c4a0fd
-- title:
--   Theorem 4 — convergence in probability of the Euler-type scheme, uniformly on [0, T]
-- statement:
--   In the setting of the SDE (2.1) and the scheme (2.2) on $[0,T]$ (Wiener martingale $W$, right-continuous filtration, $p_0,p_1\ge2$, Borel coefficients, common $\mathcal F_0$-measurable initial value $X(0)$), let $X$ solve (2.1) and $(X_n)_{n\ge1}$ solve (2.2). Suppose conditions A-1–A-4 and B-1 hold. Then
--   $$\sup_{0\le t\le T}|X_n(t)-X(t)|\xrightarrow{\ \mathbb P\ }0\qquad\text{as }n\to\infty,$$
--   that is, for every $\varepsilon>0$,
--   $$\lim_{n\to\infty}P\Big(\sup_{0\le t\le T}|X_n(t)-X(t)|>\varepsilon\Big)=0.$$
--
--   Convergence in probability requires only local conditions on the SDE and local $L^{p_0}$-approximation of the coefficients; no moment or growth condition on the scheme is involved. It is the first ingredient of the proof of Theorem 1.
--
--   **Formalization Note** The event $\{\sup_{0\le t\le T}|X_n(t)-X(t)|>\varepsilon\}$ is written as $\{\exists t\in[0,T]:\ |X_n(t)-X(t)|>\varepsilon\}$, which is the same event because the paths are continuous on $[0,T]$ and the supremum is attained. The hypotheses are exactly the printed ones (A-1–A-4 and B-1); the paper proves this theorem by citing Gyöngy and Sabanis, Theorem 4.1.
-- source:
--   Sabanis, Euler approximations with varying coefficients, arXiv:1308.1796v4, p. 6, Theorem 4

import Mathlib
import Definitions.Def_EthierKurtz_SDEState
import Definitions.Def_SabanisEuler_Shared_Setting
import Definitions.Def_SabanisEuler_LpConv_Conditions

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
open SabanisEuler.Shared

namespace SabanisEuler.LpConv

open EthierKurtz

/-- Sabanis (2016), arXiv:1308.1796v4, p. 6, Theorem 4: under A-1–A-4 and B-1 (exactly the
printed hypotheses), `sup_{0 ≤ t ≤ T} |Xₙ(t) - X(t)| → 0` in probability as `n → ∞`:
for every `ε > 0`, `P(∃ t ∈ [0, T], |Xₙ(t) - X(t)| > ε) → 0`. -/
theorem convergence_in_probability
    {d d₁ : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ℱ : Filtration ℝ≥0 mΩ) [ℱ.IsRightContinuous]
    (W : ℝ≥0 → Ω → SDEState d₁) (hW : IsWienerMartingale P ℱ W)
    (T : ℝ≥0) (hT : 0 < T)
    (p₀ p₁ : ℝ) (hp₀ : 2 ≤ p₀) (hp₁ : 2 ≤ p₁)
    (b : ℝ≥0 × SDEState d → SDEState d) (σ : ℝ≥0 × SDEState d → Diffusion d d₁)
    (hb : Measurable b) (hσ : Measurable σ)
    (bₙ : ℕ → ℝ≥0 × SDEState d → SDEState d) (σₙ : ℕ → ℝ≥0 × SDEState d → Diffusion d d₁)
    (hbₙ : ∀ n : ℕ, 1 ≤ n → Measurable (bₙ n)) (hσₙ : ∀ n : ℕ, 1 ≤ n → Measurable (σₙ n))
    (ξ : Ω → SDEState d) (hξ : Measurable[ℱ 0] ξ)
    (hA1 : CondA1 T b) (hA2 : CondA2 T b) (hA3 : CondA3 T p₁ b σ) (hA4 : CondA4 T p₀ b σ)
    (hB1 : CondB1 T p₀ b σ bₙ σₙ)
    (X : ℝ≥0 → Ω → SDEState d) (hX : IsSolution P ℱ W T ξ b σ X)
    (Xₙ : ℕ → ℝ≥0 → Ω → SDEState d)
    (hXₙ : ∀ n : ℕ, 1 ≤ n → IsSchemeSolution P ℱ W T ξ bₙ σₙ n (Xₙ n)) :
    ∀ ε : ℝ, 0 < ε → Tendsto
      (fun n : ℕ => P {ω | ∃ t ∈ Set.Icc (0 : ℝ≥0) T, ε < ‖Xₙ n t ω - X t ω‖})
      atTop (𝓝 0) := by sorry

end SabanisEuler.LpConv
