-- Prove2me | Theorems.Thm_StochKolmogorov_Classify_lemma_5_9
-- name    : StochKolmogorov.Classify.lemma_5_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T21:32:51.897965+00:00
-- url     : https://prove2.me/theorems/a17b7893-fd95-4d58-83a2-659bf0832075
-- title:
--   Lemma 5.9, p. 26 — for µ ∈ M¹, k ≥ 1, ε > 0 there is Δ > 0 with P_x{U(ω) = {µ}, ln Xᵢ(t)/t → λᵢ(µ) < 0 for i ∈ I^c_µ} > 1 − ε on K^{k,Δ}_µ
-- statement:
--   Throughout, $X$ is the solution of the stochastic Kolmogorov system $dX_i = X_i f_i(X)\,dt + X_i g_i(X)\,dE_i$, $i = 1,\dots,n$ ($n \ge 1$), on $\mathbb R^n_+ = [0,\infty)^n$, with $E = \Gamma^\top B$ for a standard Brownian motion $B$ and $\Sigma = \Gamma^\top\Gamma = (\sigma_{ij})$; $X^x$ denotes the solution started at $x$, and the coefficients satisfy Assumption 1.1 with the vector $c \in \mathbb R^{n,\circ}_+$ and the constant $\gamma_b > 0$ of (1.2). Suppose Assumption 1.4 holds, and let $\mu \in \mathcal M^1$. For every $k \in \mathbb N$, $k \ge 1$, and every $\varepsilon > 0$ there is $\Delta > 0$ such that
--   $$
--   \mathbb P_x\Big\{\mathcal U(\omega) = \{\mu\}\ \text{and}\ \lim_{t\to\infty}\frac{\ln X_i(t)}{t} = \lambda_i(\mu) < 0,\ i \in I^c_\mu\Big\} > 1-\varepsilon,\qquad x \in \mathcal K^{k,\Delta}_\mu,
--   $$
--   where $\mathcal K^{k,\Delta}_\mu = \{x \in \mathbb R^{n,\circ}_+ : k^{-1} \le x_i \le k \text{ for } i \in I_\mu,\ x_i < \Delta \text{ for } i \in I^c_\mu\}$.
--
--   A sink attracts: started close enough to the interior of its face, the process converges to $\mu$ (in the sense of occupation measures) with probability close to one, and the absent species die out exponentially fast at the rates $\lambda_i(\mu)$.
--
--   **Formalization Note** The standing setting is carried by explicit hypotheses: `hn : 0 < n`, a family `X x` of strong solutions from every $x \in \mathbb R^n_+$ driven by one Brownian motion `B` (`IsSolutionFamily`), and `Assumption11 C c γb`. Coordinates are indexed by `Fin n` (0-based), and $\|x\| = \sum_i |x_i|$ is the $\ell^1$ norm `l1` of p. 4. The page writes "$k \in \mathbb N$"; for $k = 0$ the condition $k^{-1} \le x_i$ is meaningless (in Lean $0^{-1} = 0$), and since $\mathcal K^{k,\Delta}_\mu$ grows with $k$, the statement for $k \ge 1$ loses nothing. $\Delta$ is chosen before $x$.
-- source:
--   Hening, Nguyen, Coexistence and extinction for stochastic Kolmogorov systems, arXiv:1704.06984v1, Lemma 5.9, p. 26

import Mathlib
import Definitions.Def_StochKolmogorov_Classify_Model
import Definitions.Def_StochKolmogorov_Classify_Faces
import Definitions.Def_StochKolmogorov_Classify_Classification

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace StochKolmogorov.Classify

open EthierKurtz

theorem lemma_5_9 {n : ℕ} (hn : 0 < n) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (C : Coeffs n)
    (B : ℝ≥0 → Ω → SDEState n) (X : SDEState n → ℝ≥0 → Ω → SDEState n)
    (hX : IsSolutionFamily P C B X) (c : SDEState n) (γb : ℝ) (hA : Assumption11 C c γb)
    (δ₁ : ℝ) (h14 : Assumption14 C δ₁) :
    ∀ μ ∈ M1 P C X, ∀ k : ℕ, 1 ≤ k → ∀ ε : ℝ, 0 < ε → ∃ Δ : ℝ, 0 < Δ ∧
      ∀ x ∈ Kbox μ k Δ, 1 - ε < (P (extinctEvent C X x μ)).toReal := by sorry

end StochKolmogorov.Classify
