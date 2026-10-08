-- Prove2me | Theorems.Thm_TDApprox_Conv_lemma_2
-- name    : TDApprox.Conv.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:50:57.657183+00:00
-- url     : https://prove2.me/theorems/6fb12791-896e-4a84-9911-47fb125fd6e8
-- title:
--   Lemma 2, p. 12 — under Assumption 1(a)–(b), J* is well defined and finite, J* ∈ L₂(S, D), and J* = Σ_t (αP)^t ḡ
-- statement:
--   Let a Markov chain on a countable state space $S$ have transition matrix $P$, transition costs $g(i,j)$ and discount factor $\alpha \in (0,1)$. Suppose that it has a unique invariant distribution $\pi$ with $\pi(i) > 0$ for all $i$ (Assumption 1(a)), and that $E_0[g^2(i_t,i_{t+1})] < \infty$ under the stationary law (Assumption 1(b)). Let $\bar g(i) = E[g(i_t,i_{t+1}) \mid i_t = i] = \sum_j p_{ij}g(i,j)$ and
--   $$J^*(i) = E\Big[\sum_{t=0}^\infty \alpha^t g(i_t,i_{t+1}) \,\Big|\, i_0 = i\Big].$$
--
--   Then:
--   1. for every $i$, $E\big[\sum_{t=0}^\infty \alpha^t|g(i_t,i_{t+1})| \mid i_0 = i\big] < \infty$, so $J^*(i)$ is well defined and finite (Assumption 1(c) holds);
--   2. $\bar g$ and every $P^t\bar g$ are well defined;
--   3. $J^* \in L_2(S,D)$;
--   4. at every state,
--   $$J^* = \sum_{t=0}^\infty (\alpha P)^t \bar g.$$
--
--   The lemma shows that Assumption 1(c) is a consequence of 1(a)–(b) and puts $J^*$ in the space in which the analysis runs.
--
--   **Formalization Note.** "$J^*(i)$ well defined and finite" is the absolute integrability of the discounted cost series under the path law from $i$, the same reading as Assumption 1(c). The series identity is stated pointwise, with $(P^t\bar g)(i)$ the integral of $\bar g$ against the $t$-step law from $i$.
-- source:
--   Tsitsiklis & Van Roy, LIDS-P-2322 (1996), Lemma 2, p. 12 (ḡ defined in the sentence before it)

import Mathlib
import Definitions.Def_TDApprox_Conv_Model
open MeasureTheory ProbabilityTheory Filter Topology Finset Matrix

namespace TDApprox.Conv

/-- **Lemma 2** (Tsitsiklis & Van Roy, LIDS-P-2322 (1996), p. 12). Under Assumptions 1(a)–(b),
`J*(i)` is well defined and finite for every `i` (the absolute series
`E[Σ_t α^t |g(i_t, i_{t+1})| | i_0 = i]` is finite, i.e. Assumption 1(c) holds), `J* ∈ L₂(S, D)`,
and `J* = Σ_{t ≥ 0} (αP)^t ḡ` with `ḡ(i) = E[g(i_t, i_{t+1}) | i_t = i]`. The conclusion also
records that `ḡ` and `P^t ḡ` are well defined. -/
theorem lemma_2 {S : Type*} [MeasurableSpace S] [DiscreteMeasurableSpace S] [Countable S]
    (P : Kernel S S) [IsMarkovKernel P] (π : Measure S) [IsProbabilityMeasure π]
    (g : S → S → ℝ) (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1)
    (h1a : Assumption1a P π) (h1b : Assumption1b P π g) :
    Assumption1c P g α ∧
    (∀ i, Integrable (g i) (P i)) ∧
    (∀ i t, Integrable (gbar P g) ((P ^ t) i)) ∧
    MemL2D π (Jstar P g α) ∧
    ∀ i, HasSum (fun t : ℕ => α ^ t * ∫ j, gbar P g j ∂((P ^ t) i)) (Jstar P g α i) := by sorry

end TDApprox.Conv
