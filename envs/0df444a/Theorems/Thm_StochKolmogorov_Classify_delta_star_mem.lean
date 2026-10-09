-- Prove2me | Theorems.Thm_StochKolmogorov_Classify_delta_star_mem
-- name    : StochKolmogorov.Classify.delta_star_mem
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T21:32:36.56788+00:00
-- url     : https://prove2.me/theorems/03736621-7486-4244-bced-1a023ff9579a
-- title:
--   §1.1, p. 5 — the Dirac measure δ* at the origin belongs to M, so M ≠ ∅
-- statement:
--   Throughout, $X$ is the solution of the stochastic Kolmogorov system $dX_i = X_i f_i(X)\,dt + X_i g_i(X)\,dE_i$, $i = 1,\dots,n$ ($n \ge 1$), on $\mathbb R^n_+ = [0,\infty)^n$, with $E = \Gamma^\top B$ for a standard Brownian motion $B$ and $\Sigma = \Gamma^\top\Gamma = (\sigma_{ij})$; $X^x$ denotes the solution started at $x$, and the coefficients satisfy Assumption 1.1 with the vector $c \in \mathbb R^{n,\circ}_+$ and the constant $\gamma_b > 0$ of (1.2). Let $\delta^*$ be the Dirac measure at the origin $0$. Then
--   $$
--   \delta^* \in \mathcal M,
--   $$
--   i.e. $\delta^*$ is an ergodic invariant probability measure of $X$ supported on $\partial\mathbb R^n_+$.
--
--   The origin is an equilibrium of (1.1), since every coefficient carries a factor $x_i$. This fact guarantees that $\mathcal M$ is never empty, and it is the starting point of the case $\mathcal M^2 = \emptyset$ in the proof of Theorem 5.2.
--
--   **Formalization Note** The standing setting is carried by explicit hypotheses: `hn : 0 < n`, a family `X x` of strong solutions from every $x \in \mathbb R^n_+$ driven by one Brownian motion `B` (`IsSolutionFamily`), and `Assumption11 C c γb`. Coordinates are indexed by `Fin n` (0-based), and $\|x\| = \sum_i |x_i|$ is the $\ell^1$ norm `l1` of p. 4.
-- source:
--   Hening, Nguyen, Coexistence and extinction for stochastic Kolmogorov systems, arXiv:1704.06984v1, §1.1, p. 5 ("Note that if we let δ* be the Dirac measure concentrated at 0 then δ* ∈ M so that M ≠ ∅.")

import Mathlib
import Definitions.Def_StochKolmogorov_Classify_Model
import Definitions.Def_StochKolmogorov_Classify_Faces
import Definitions.Def_StochKolmogorov_Classify_Classification

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace StochKolmogorov.Classify

open EthierKurtz

theorem delta_star_mem {n : ℕ} (hn : 0 < n) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (C : Coeffs n)
    (B : ℝ≥0 → Ω → SDEState n) (X : SDEState n → ℝ≥0 → Ω → SDEState n)
    (hX : IsSolutionFamily P C B X) (c : SDEState n) (γb : ℝ) (hA : Assumption11 C c γb) :
    Measure.dirac (0 : SDEState n) ∈ bdryErgodic P X := by sorry

end StochKolmogorov.Classify
