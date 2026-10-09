-- Prove2me | Theorems.Thm_StochKolmogorov_Classify_case_M2_empty
-- name    : StochKolmogorov.Classify.case_M2_empty
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T21:32:42.976409+00:00
-- url     : https://prove2.me/theorems/fc17103a-f09c-4885-9410-752a413e1800
-- title:
--   Proof of Theorem 5.2, pp. 28–29 — if M¹ ≠ ∅ and M² = ∅ then M = M¹ = {δ*}
-- statement:
--   Throughout, $X$ is the solution of the stochastic Kolmogorov system $dX_i = X_i f_i(X)\,dt + X_i g_i(X)\,dE_i$, $i = 1,\dots,n$ ($n \ge 1$), on $\mathbb R^n_+ = [0,\infty)^n$, with $E = \Gamma^\top B$ for a standard Brownian motion $B$ and $\Sigma = \Gamma^\top\Gamma = (\sigma_{ij})$; $X^x$ denotes the solution started at $x$, and the coefficients satisfy Assumption 1.1 with the vector $c \in \mathbb R^{n,\circ}_+$ and the constant $\gamma_b > 0$ of (1.2). Suppose Assumption 1.4 holds, $\mathcal M^1 \ne \emptyset$ and $\mathcal M^2 = \emptyset$. Then
--   $$
--   \mathcal M^1 = \{\delta^*\}\qquad\text{and}\qquad \mathcal M = \{\delta^*\},
--   $$
--   where $\delta^*$ is the Dirac measure at the origin.
--
--   In this case all species go extinct: the only boundary ergodic measure is the origin, and it is a sink. This is the second case of the proof of Theorem 5.2.
--
--   **Formalization Note** The standing setting is carried by explicit hypotheses: `hn : 0 < n`, a family `X x` of strong solutions from every $x \in \mathbb R^n_+$ driven by one Brownian motion `B` (`IsSolutionFamily`), and `Assumption11 C c γb`. Coordinates are indexed by `Fin n` (0-based), and $\|x\| = \sum_i |x_i|$ is the $\ell^1$ norm `l1` of p. 4. The page argues this inside the proof of Theorem 5.2, under Assumptions 1.1, 1.4 and 1.5; Assumption 1.4 is retained because it is a standing hypothesis of that theorem (Assumption 1.5 holds automatically when $\mathcal M^2 = \emptyset$).
-- source:
--   Hening, Nguyen, Coexistence and extinction for stochastic Kolmogorov systems, arXiv:1704.06984v1, proof of Theorem 5.2, pp. 28–29

import Mathlib
import Definitions.Def_StochKolmogorov_Classify_Model
import Definitions.Def_StochKolmogorov_Classify_Faces
import Definitions.Def_StochKolmogorov_Classify_Classification

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace StochKolmogorov.Classify

open EthierKurtz

theorem case_M2_empty {n : ℕ} (hn : 0 < n) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (C : Coeffs n)
    (B : ℝ≥0 → Ω → SDEState n) (X : SDEState n → ℝ≥0 → Ω → SDEState n)
    (hX : IsSolutionFamily P C B X) (c : SDEState n) (γb : ℝ) (hA : Assumption11 C c γb)
    (δ₁ : ℝ) (h14 : Assumption14 C δ₁)
    (hM2 : M2 P C X = ∅) (hM1 : (M1 P C X).Nonempty) :
    M1 P C X = {Measure.dirac (0 : SDEState n)} ∧
      bdryErgodic P X = {Measure.dirac (0 : SDEState n)} := by sorry

end StochKolmogorov.Classify
