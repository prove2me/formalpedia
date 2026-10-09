-- Prove2me | Theorems.Thm_StochKolmogorov_Classify_lemma_5_7
-- name    : StochKolmogorov.Classify.lemma_5_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T21:32:53.168382+00:00
-- url     : https://prove2.me/theorems/e6f4d41d-d6e5-446e-bad8-3ab39f133d9d
-- title:
--   Lemma 5.7, p. 25 — {Π̃_t, t ≥ 1} is tight and its weak*-limit set U(ω) consists of invariant probability measures of X, with probability 1
-- statement:
--   Throughout, $X$ is the solution of the stochastic Kolmogorov system $dX_i = X_i f_i(X)\,dt + X_i g_i(X)\,dE_i$, $i = 1,\dots,n$ ($n \ge 1$), on $\mathbb R^n_+ = [0,\infty)^n$, with $E = \Gamma^\top B$ for a standard Brownian motion $B$ and $\Sigma = \Gamma^\top\Gamma = (\sigma_{ij})$; $X^x$ denotes the solution started at $x$, and the coefficients satisfy Assumption 1.1 with the vector $c \in \mathbb R^{n,\circ}_+$ and the constant $\gamma_b > 0$ of (1.2). Suppose Assumption 1.4 holds. For every initial condition $X(0) = x \in \mathbb R^n_+$, with probability 1:
--
--   1. the family of random occupation measures $\{\widetilde\Pi_t(\cdot), t \ge 1\}$ is tight, and
--   2. every measure in its weak\*-limit set $\mathcal U(\omega)$ is an invariant probability measure of $X$.
--
--   This is the bridge from the sample-path behaviour of $X$ to its invariant measures: every long-run empirical distribution of a path is stationary for the dynamics.
--
--   **Formalization Note** The standing setting is carried by explicit hypotheses: `hn : 0 < n`, a family `X x` of strong solutions from every $x \in \mathbb R^n_+$ driven by one Brownian motion `B` (`IsSolutionFamily`), and `Assumption11 C c γb`. Coordinates are indexed by `Fin n` (0-based), and $\|x\| = \sum_i |x_i|$ is the $\ell^1$ norm `l1` of p. 4. Tightness is Mathlib's `IsTightMeasureSet` on $\mathbb R^n$; the occupation measures live on $\mathbb R^n_+$ almost surely, so this is tightness in $\mathbb R^n_+$. The paper's proof cites [SBA11, Theorems 4, 5] and [EHS15, Theorem 4.2] for part 2.
-- source:
--   Hening, Nguyen, Coexistence and extinction for stochastic Kolmogorov systems, arXiv:1704.06984v1, Lemma 5.7, p. 25

import Mathlib
import Definitions.Def_StochKolmogorov_Classify_Model
import Definitions.Def_StochKolmogorov_Classify_Faces
import Definitions.Def_StochKolmogorov_Classify_Classification

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace StochKolmogorov.Classify

open EthierKurtz

theorem lemma_5_7 {n : ℕ} (hn : 0 < n) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (C : Coeffs n)
    (B : ℝ≥0 → Ω → SDEState n) (X : SDEState n → ℝ≥0 → Ω → SDEState n)
    (hX : IsSolutionFamily P C B X) (c : SDEState n) (γb : ℝ) (hA : Assumption11 C c γb)
    (δ₁ : ℝ) (h14 : Assumption14 C δ₁) :
    ∀ x ∈ orthant n, ∀ᵐ ω ∂P,
      IsTightMeasureSet {μ | ∃ t : ℝ, 1 ≤ t ∧ μ = occ X x t ω} ∧
        ∀ π ∈ limitSet X x ω, IsInvariant P X π := by sorry

end StochKolmogorov.Classify
