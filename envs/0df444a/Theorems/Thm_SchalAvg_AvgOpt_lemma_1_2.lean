-- Prove2me | Theorems.Thm_SchalAvg_AvgOpt_lemma_1_2
-- name    : SchalAvg.AvgOpt.lemma_1_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:50:40.496818+00:00
-- url     : https://prove2.me/theorems/4122257e-3063-42f6-a878-42314a546865
-- title:
--   Lemma 1.2 — the Tauberian inequality limsup (1 − β)J_β ≤ Φ, and g̲ ≤ ḡ ≤ g < ∞
-- statement:
--   Consider Schäl's decision model $(S, A, A(\cdot), q, c)$ with standard Borel state and action spaces and costs in $[0, \infty]$. For an admissible policy $\delta$ and an initial state $x$ let $J_\beta(\delta, x)$ be the expected total $\beta$-discounted cost and $\Phi(\delta, x) = \limsup_n \frac1n J^n(\delta, x)$ the average expected cost per unit time. Let $g$, $\bar g$, $\underline g$ be the minimal average cost and the upper and lower limits of $(1-\beta) m_\beta$ as $\beta \uparrow 1$.
--
--   1. (Tauberian relation) For every admissible $\delta$ and every $x \in S$,
--   $$\limsup_{\beta \to 1} (1 - \beta) J_\beta(\delta, x) \le \Phi(\delta, x).$$
--   2. Under the General Assumption $g < \infty$,
--   $$0 \le \underline g \le \bar g \le g < \infty.$$
--
--   Part 2 says that the vanishing-discount limits of $(1-\beta)m_\beta$ never exceed the optimal average cost; it is the lower half of every "average optimal" conclusion of the paper.
--
--   **Formalization Note.** All quantities lie in $[0, \infty]$, so $0 \le \underline g$ is automatic, and $g < \infty$ in part 2 is the General Assumption itself; the content of part 2 is $\underline g \le \bar g \le g$. $\beta \to 1$ is the left limit `𝓝[<] 1`; the factor $(1 - \beta)$ is `ENNReal.ofReal (1 - β)`. Part 1 is stated for admissible policies, the paper's class $\Delta$.
-- source:
--   Schäl, Average Optimality in Dynamic Programming with General State Space, Math. Oper. Res. 18(1) (1993), p. 164, Lemma 1.2

import Mathlib
import Definitions.Def_FeinbergLiang_ACOE_MDP
import Definitions.Def_SchalAvg_AvgOpt_Model

open scoped ENNReal NNReal Topology
open MeasureTheory ProbabilityTheory Filter FeinbergLiang.ACOE

namespace SchalAvg.AvgOpt

theorem lemma_1_2 {S A : Type*} [MeasurableSpace S] [StandardBorelSpace S]
    [MeasurableSpace A] [StandardBorelSpace A] (M : Model S A) :
    (∀ π : Policy S A, Admissible M π → ∀ x : S,
      limsup (fun β : ℝ => ENNReal.ofReal (1 - β) * Jbeta M π β x) (𝓝[<] 1) ≤ Phi M π x) ∧
    (GeneralAssumption M → gLower M ≤ gUpper M ∧ gUpper M ≤ gStar M ∧ gStar M < ⊤) := by sorry

end SchalAvg.AvgOpt
