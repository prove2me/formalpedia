-- Prove2me | Theorems.Thm_RGMISFast_prescribed_extension_drift
-- name    : RGMISFast.prescribed_extension_drift
-- status  : Proved
-- author  : @srikkanthr
-- created : 2026-11-15T23:54:34.991301+00:00
-- url     : https://prove2.me/theorems/ba797800-08e6-49b0-b12e-378ee91e4872
-- title:
--   Prescribed-rank extension counts satisfy the nonlinear decay inequality
-- statement:
--   In the setting of Lemma 5.3, fix $k\ge1$ and put $T=a-\theta>0$. Under the explicit law conditioned on the history at $\theta$ and the prescribed seed ranks, let
--   $$f(s)=\mathbb E[N_k(A;G_{\theta+s})],\qquad 0\le s\le T.$$
--   The expectation is finite, $f$ is nonnegative and continuous on $[0,T]$, and it has a derivative on $(0,T)$ satisfying
--   $$f'(s)\le-\frac{k}{e}f(s)^{1+1/k}.$$
--   The formal statement supplies real functions $f,f'$ and identifies the lower integral with $\operatorname{ofReal}(f(s))$ at every point of the interval, so finiteness of the expectation is explicitly part of the assertion. This is the stochastic differential-inequality step in the proof of Lemma 5.3, before integrating the inequality. It includes the identically-zero case; no strict positivity assumption is imposed.
-- source:
--   Dalirrooyfard, Makarychev, Mitrović, Ramachandran, Randomized Greedy MIS Is Fast at Every Node, §5.2, Lemma 5.3 and its proof, printed pp.20–21 (PDF pp.22–23). The short-window arrival derivative, contraction of A, Lemma 5.1, and Jensen inequality precede the final inverse-power integration.

import Mathlib
import Definitions.Def_RGMISFast_Y
import Definitions.Def_RGMISFast_condLaw

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open RGMISFast

theorem RGMISFast.prescribed_extension_drift {V : Type*} [Fintype V] [LinearOrder V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (θ a : ℝ) (hθ : 0 ≤ θ) (hθa : θ < a) (r₀ : V → ℝ)
    (hr₀ : IsHistory r₀ θ) (A : Finset V) (hA : IsConnectedSet G A)
    (hAθ : ActiveAt G r₀ θ A) (rA : V → ℝ) (hrA : ∀ v ∈ A, a ≤ rA v) (k : ℕ) (hk : 1 ≤ k) :
    ∃ f f' : ℝ → ℝ,
      (∀ s ∈ Set.Icc 0 (a-θ),
        (∫⁻ r, (Ncount G A k (θ+s) r : ℝ≥0∞) ∂(condLaw r₀ θ A rA)) = ENNReal.ofReal (f s)) ∧
      ContinuousOn f (Set.Icc 0 (a-θ)) ∧
      (∀ s ∈ Set.Icc 0 (a-θ), 0 ≤ f s) ∧
      (∀ s ∈ Set.Ioo 0 (a-θ), HasDerivAt f (f' s) s) ∧
      (∀ s ∈ Set.Ioo 0 (a-θ),
        f' s ≤ -(k:ℝ) / Real.exp 1 * f s ^ (1+(k:ℝ)⁻¹)) := by sorry
