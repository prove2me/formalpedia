-- Prove2me | Theorems.Thm_StochKolmogorov_Classify_lemma_5_8
-- name    : StochKolmogorov.Classify.lemma_5_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T21:32:46.043475+00:00
-- url     : https://prove2.me/theorems/111ef3e2-59f2-4e17-9af1-adf962c070bc
-- title:
--   Lemma 5.8, p. 25 — for µ ∈ M¹ and x ∈ ℝⁿ,◦₊, P_x{U(ω) ⊂ Conv(M_µ ∪ {µ})} = P_x{U(ω) = {µ}}
-- statement:
--   Throughout, $X$ is the solution of the stochastic Kolmogorov system $dX_i = X_i f_i(X)\,dt + X_i g_i(X)\,dE_i$, $i = 1,\dots,n$ ($n \ge 1$), on $\mathbb R^n_+ = [0,\infty)^n$, with $E = \Gamma^\top B$ for a standard Brownian motion $B$ and $\Sigma = \Gamma^\top\Gamma = (\sigma_{ij})$; $X^x$ denotes the solution started at $x$, and the coefficients satisfy Assumption 1.1 with the vector $c \in \mathbb R^{n,\circ}_+$ and the constant $\gamma_b > 0$ of (1.2). Suppose Assumption 1.4 holds, and let $\mu \in \mathcal M^1$. For every $x \in \mathbb R^{n,\circ}_+$,
--   $$
--   \mathbb P_x\big\{\mathcal U(\omega) \subset \mathrm{Conv}(\mathcal M_\mu\cup\{\mu\})\big\} = \mathbb P_x\big\{\mathcal U(\omega) = \{\mu\}\big\}.
--   $$
--
--   Once the empirical measures of a path concentrate on the face of a sink $\mu$, condition (1.7) pushes them off the lower-dimensional boundary of that face, so they can only accumulate at $\mu$ itself. This is the key step of Lemma 5.9.
--
--   **Formalization Note** The standing setting is carried by explicit hypotheses: `hn : 0 < n`, a family `X x` of strong solutions from every $x \in \mathbb R^n_+$ driven by one Brownian motion `B` (`IsSolutionFamily`), and `Assumption11 C c γb`. Coordinates are indexed by `Fin n` (0-based), and $\|x\| = \sum_i |x_i|$ is the $\ell^1$ norm `l1` of p. 4. $\mathrm{Conv}$ is the set of finite convex combinations with positive weights, as defined on p. 5. Probabilities of events are written with the measure $P$ applied to the event (its outer measure); measurability of the events is not claimed by the paper and is not asserted.
-- source:
--   Hening, Nguyen, Coexistence and extinction for stochastic Kolmogorov systems, arXiv:1704.06984v1, Lemma 5.8, p. 25

import Mathlib
import Definitions.Def_StochKolmogorov_Classify_Model
import Definitions.Def_StochKolmogorov_Classify_Faces
import Definitions.Def_StochKolmogorov_Classify_Classification

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace StochKolmogorov.Classify

open EthierKurtz

theorem lemma_5_8 {n : ℕ} (hn : 0 < n) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (C : Coeffs n)
    (B : ℝ≥0 → Ω → SDEState n) (X : SDEState n → ℝ≥0 → Ω → SDEState n)
    (hX : IsSolutionFamily P C B X) (c : SDEState n) (γb : ℝ) (hA : Assumption11 C c γb)
    (δ₁ : ℝ) (h14 : Assumption14 C δ₁) :
    ∀ μ ∈ M1 P C X, ∀ x ∈ openOrthant n,
      P {ω | limitSet X x ω ⊆ conv (subErgodic P X μ ∪ {μ})}
        = P {ω | limitSet X x ω = {μ}} := by sorry

end StochKolmogorov.Classify
