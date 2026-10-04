-- Prove2me | Theorems.Thm_StochApproxDyn_LimitSet_isAsymptoticPseudotrajectory_characterization
-- name    : StochApproxDyn.LimitSet.isAsymptoticPseudotrajectory_characterization
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T07:03:17.47223+00:00
-- url     : https://prove2.me/theorems/5a161b7e-faf4-4830-a196-2a7db1552d49
-- title:
--   Theorem 3.2 — characterization of precompact asymptotic pseudotrajectories
-- statement:
--   Let $\Phi$ be a semiflow on a metric space $(M,d)$ and let $X:\mathbb R_+\to M$ be a continuous function whose image has compact closure in $M$. Consider the assertions
--
--   1. $X$ is an asymptotic pseudotrajectory of $\Phi$;
--   2. $X$ is uniformly continuous, and every limit point of $\{\Theta^t(X)\}$ lies in $S_\Phi$, i.e. whenever $t_k\to\infty$ and $\Theta^{t_k}(X)\to Y$ in $C^0(\mathbb R_+,M)$, then $Y=\Phi^p$ for some $p\in M$;
--   3. the family $\{\Theta^t(X)\}_{t\ge0}$ is relatively compact in $C^0(\mathbb R_+,M)$.
--
--   Then (1) and (2) are equivalent, and they imply (3):
--   $$(1)\iff(2),\qquad (1)\implies(3).$$
--
--   This identifies precompact asymptotic pseudotrajectories as the uniformly continuous curves whose long-run translates look like trajectories of $\Phi$, and supplies the compactness needed for the limit set theorem.
--
--   **Formalization Note** $C^0(\mathbb R_+,M)$ is Mathlib's `C(ℝ≥0, M)` with the compact-open topology, which is the topology of uniform convergence on compact intervals and is the topology of the distance $d$. Limit points are limits along sequences $t_k\to\infty$, $k\in\mathbb N$. Relative compactness is compactness of the closure of $\{\Theta^t(X):t\ge0\}$. The source states the result on $C^0(\mathbb R,M)$; for a semiflow that version is false (see Lemma 3.1), and the half-line reading is used.
-- source:
--   Benaïm, Dynamics of Stochastic Approximation Algorithms, Séminaire de Probabilités XXXIII, LNM 1709 (1999), pp. 10–11, Theorem 3.2 and its footnote 1 (read on C⁰(ℝ₊, M))

import Mathlib
import Definitions.Def_StochApproxDyn_LimitSet_AsymptoticPseudotrajectory
import Definitions.Def_StochApproxDyn_LimitSet_TranslationSemiflow

open scoped NNReal

namespace StochApproxDyn.LimitSet

/-- Theorem 3.2 (Benaïm 1999, pp. 10–11), on `C⁰(ℝ₊, M)` with the compact-open topology
(uniform convergence on compact intervals). For a continuous `X : ℝ₊ → M` with relatively compact
image: (i) `X` is an asymptotic pseudotrajectory of `Φ` iff (ii) `X` is uniformly continuous and
every limit point `Y = lim_k Θ^{t_k}(X)`, `t_k → ∞`, lies in `S_Φ`; and (i) implies
(iii) `{Θ^t(X)}_{t ≥ 0}` is relatively compact. -/
theorem isAsymptoticPseudotrajectory_characterization {M : Type*} [MetricSpace M]
    (Φ : Flow ℝ≥0 M) (X : C(ℝ≥0, M)) (hX : IsCompact (closure (Set.range X))) :
    (IsAsymptoticPseudotrajectory Φ X ↔
      (UniformContinuous X ∧
        ∀ Y : C(ℝ≥0, M), (∃ τ : ℕ → ℝ≥0, Filter.Tendsto τ Filter.atTop Filter.atTop ∧
            Filter.Tendsto (fun k => translate (τ k) X) Filter.atTop (nhds Y)) →
          Y ∈ trajectorySpace Φ)) ∧
    (IsAsymptoticPseudotrajectory Φ X →
      IsCompact (closure (Set.range fun t : ℝ≥0 => translate t X))) := by sorry

end StochApproxDyn.LimitSet
