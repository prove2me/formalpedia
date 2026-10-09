-- Prove2me | Theorems.Thm_StochKolmogorov_Classify_lemma_5_5
-- name    : StochKolmogorov.Classify.lemma_5_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T21:32:46.9025+00:00
-- url     : https://prove2.me/theorems/6b6c1b73-348f-460e-bad6-fd928947423a
-- title:
--   Lemma 5.5, p. 25 — there is K̂₁ > 1 with liminf (1/t)∫₀ᵗ 1{‖X(s)‖ ≤ K̂₁} ds ≥ 1/2 a.s., and (5.19) Xᵢ stays above some β > 0 on a finite horizon with probability > 1 − ε₁
-- statement:
--   Throughout, $X$ is the solution of the stochastic Kolmogorov system $dX_i = X_i f_i(X)\,dt + X_i g_i(X)\,dE_i$, $i = 1,\dots,n$ ($n \ge 1$), on $\mathbb R^n_+ = [0,\infty)^n$, with $E = \Gamma^\top B$ for a standard Brownian motion $B$ and $\Sigma = \Gamma^\top\Gamma = (\sigma_{ij})$; $X^x$ denotes the solution started at $x$, and the coefficients satisfy Assumption 1.1 with the vector $c \in \mathbb R^{n,\circ}_+$ and the constant $\gamma_b > 0$ of (1.2). Suppose Assumption 1.4 holds. There is $\widehat K_1 > 1$ such that
--
--   1. (5.18) for every $x \in \mathbb R^n_+$, almost surely
--   $$
--   \liminf_{t\to\infty}\frac1t\int_0^t\mathbf 1_{\{\|X^x(s)\|\le\widehat K_1\}}\,ds \ge \frac12 ;
--   $$
--   2. (5.19) for every horizon $T > 0$ and all $\varepsilon_1, \varepsilon_2 > 0$ there is $\beta > 0$ such that, for each $i = 1,\dots,n$,
--   $$
--   \mathbb P_x\{X_i(t) > \beta\ \ \forall t \in [0,T]\} > 1-\varepsilon_1\qquad\text{whenever } x \in \mathbb R^n_+,\ \|x\| \le \widehat K_1,\ x_i > \varepsilon_2 .
--   $$
--
--   The first part says the process spends at least half of its time in a fixed compact set; the second says it cannot get close to the face $\{x_i = 0\}$ quickly when started away from it. Both are used in the proof of Lemma 5.9.
--
--   **Formalization Note** The standing setting is carried by explicit hypotheses: `hn : 0 < n`, a family `X x` of strong solutions from every $x \in \mathbb R^n_+$ driven by one Brownian motion `B` (`IsSolutionFamily`), and `Assumption11 C c γb`. Coordinates are indexed by `Fin n` (0-based), and $\|x\| = \sum_i |x_i|$ is the $\ell^1$ norm `l1` of p. 4. The paper states (5.19) for the horizon $n_eT_e$, a constant defined in Lemma 5.2 for a measure satisfying Assumption 1.3, which is not among the hypotheses of Lemma 5.5; the statement here is for every horizon $T > 0$, which contains the printed one and is what the proof ((B.8)–(B.9), p. 36) gives. $\widehat K_1$ is chosen before everything else; $\beta$ after $T, \varepsilon_1, \varepsilon_2$ and before $i$ and $x$. The $\liminf \ge 1/2$ is written as: for every $\varepsilon > 0$, eventually the time spent in $\{\|x\| \le \widehat K_1\}$ up to $t$ is at least $(1/2-\varepsilon)t$.
-- source:
--   Hening, Nguyen, Coexistence and extinction for stochastic Kolmogorov systems, arXiv:1704.06984v1, Lemma 5.5, (5.18)–(5.19), p. 25 (proof in Appendix B, pp. 35–36)

import Mathlib
import Definitions.Def_StochKolmogorov_Classify_Model
import Definitions.Def_StochKolmogorov_Classify_Faces
import Definitions.Def_StochKolmogorov_Classify_Classification

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace StochKolmogorov.Classify

open EthierKurtz

theorem lemma_5_5 {n : ℕ} (hn : 0 < n) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (C : Coeffs n)
    (B : ℝ≥0 → Ω → SDEState n) (X : SDEState n → ℝ≥0 → Ω → SDEState n)
    (hX : IsSolutionFamily P C B X) (c : SDEState n) (γb : ℝ) (hA : Assumption11 C c γb)
    (δ₁ : ℝ) (h14 : Assumption14 C δ₁) :
    ∃ Khat1 : ℝ, 1 < Khat1 ∧
      (∀ x ∈ orthant n, ∀ᵐ ω ∂P, ∀ ε : ℝ, 0 < ε → ∀ᶠ t : ℝ in atTop,
        ENNReal.ofReal ((1 / 2 - ε) * t)
          ≤ volume {s : ℝ | s ∈ Set.Icc (0 : ℝ) t ∧ l1 (X x s.toNNReal ω) ≤ Khat1}) ∧
      ∀ T : ℝ, 0 < T → ∀ ε₁ : ℝ, 0 < ε₁ → ∀ ε₂ : ℝ, 0 < ε₂ → ∃ β : ℝ, 0 < β ∧
        ∀ i, ∀ x ∈ orthant n, l1 x ≤ Khat1 → ε₂ < x i →
          1 - ε₁ < (P {ω | ∀ t : ℝ≥0, (t : ℝ) ≤ T → β < X x t ω i}).toReal := by sorry

end StochKolmogorov.Classify
