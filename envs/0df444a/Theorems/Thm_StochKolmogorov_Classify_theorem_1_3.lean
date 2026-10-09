-- Prove2me | Theorems.Thm_StochKolmogorov_Classify_theorem_1_3
-- name    : StochKolmogorov.Classify.theorem_1_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T21:32:48.971344+00:00
-- url     : https://prove2.me/theorems/8f909832-08c5-4806-ba4c-d17124712878
-- title:
--   Theorem 1.3, p. 8 — under Assumptions 1.1, 1.4, 1.5 and M¹ ≠ ∅, from every interior point Σ_{µ∈M¹} P^µ_x = 1 and each P^µ_x > 0
-- statement:
--   Throughout, $X$ is the solution of the stochastic Kolmogorov system $dX_i = X_i f_i(X)\,dt + X_i g_i(X)\,dE_i$, $i = 1,\dots,n$ ($n \ge 1$), on $\mathbb R^n_+ = [0,\infty)^n$, with $E = \Gamma^\top B$ for a standard Brownian motion $B$ and $\Sigma = \Gamma^\top\Gamma = (\sigma_{ij})$; $X^x$ denotes the solution started at $x$, and the coefficients satisfy Assumption 1.1 with the vector $c \in \mathbb R^{n,\circ}_+$ and the constant $\gamma_b > 0$ of (1.2). Suppose Assumptions 1.4 and 1.5 hold and $\mathcal M^1 \ne \emptyset$. For $x \in \mathbb R^{n,\circ}_+$ and $\mu \in \mathcal M^1$ let
--   $$
--   P^\mu_x := \mathbb P_x\Big\{\mathcal U(\omega) = \{\mu\}\ \text{and}\ \lim_{t\to\infty}\frac{\ln X_i(t)}{t} = \lambda_i(\mu) < 0,\ i \in I^c_\mu\Big\},
--   $$
--   where $\mathcal U(\omega)$ is the weak\*-limit set of the occupation measures $\{\widetilde\Pi_t(\omega), t \ge 1\}$. Then for every $x \in \mathbb R^{n,\circ}_+$
--   $$
--   \sum_{\mu\in\mathcal M^1} P^\mu_x = 1,\qquad\text{and}\qquad P^\mu_x > 0 \ \text{ for every } \mu \in \mathcal M^1 .
--   $$
--
--   Almost surely the empirical distribution of the path converges to a single sink $\mu \in \mathcal M^1$, the species absent from $\mu$ die out at the exponential rates $\lambda_i(\mu) < 0$, and every sink is reached with positive probability. This answers which species go extinct and which survive when the community does not persist.
--
--   **Formalization Note** The standing setting is carried by explicit hypotheses: `hn : 0 < n`, a family `X x` of strong solutions from every $x \in \mathbb R^n_+$ driven by one Brownian motion `B` (`IsSolutionFamily`), and `Assumption11 C c γb`. Coordinates are indexed by `Fin n` (0-based), and $\|x\| = \sum_i |x_i|$ is the $\ell^1$ norm `l1` of p. 4. The sum over $\mathcal M^1$ is an unconditional sum in $[0,\infty]$ over the set $\mathcal M^1$, with no finiteness assumption on $\mathcal M^1$; the events for distinct $\mu$ are disjoint, since $\mathcal U(\omega) = \{\mu\}$ determines $\mu$. Probabilities are the measure $P$ applied to the events; measurability is not asserted. Assumption 1.4 enters with any $\delta_1 > 0$ (the paper's "$\delta_1 \le \delta_0$" is without loss of generality, since the limit persists for smaller $\delta_1$).
-- source:
--   Hening, Nguyen, Coexistence and extinction for stochastic Kolmogorov systems, arXiv:1704.06984v1, Theorem 1.3, p. 8 (= Theorem 5.2, p. 28)

import Mathlib
import Definitions.Def_StochKolmogorov_Classify_Model
import Definitions.Def_StochKolmogorov_Classify_Faces
import Definitions.Def_StochKolmogorov_Classify_Classification

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace StochKolmogorov.Classify

open EthierKurtz

theorem theorem_1_3 {n : ℕ} (hn : 0 < n) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (C : Coeffs n)
    (B : ℝ≥0 → Ω → SDEState n) (X : SDEState n → ℝ≥0 → Ω → SDEState n)
    (hX : IsSolutionFamily P C B X) (c : SDEState n) (γb : ℝ) (hA : Assumption11 C c γb)
    (δ₁ : ℝ) (h14 : Assumption14 C δ₁) (h15 : Assumption15 P C X) (hM1 : (M1 P C X).Nonempty) :
    ∀ x ∈ openOrthant n,
      (∑' μ : M1 P C X, P (extinctEvent C X x (μ : Measure (SDEState n)))) = 1 ∧
        ∀ μ ∈ M1 P C X, 0 < P (extinctEvent C X x μ) := by sorry

end StochKolmogorov.Classify
