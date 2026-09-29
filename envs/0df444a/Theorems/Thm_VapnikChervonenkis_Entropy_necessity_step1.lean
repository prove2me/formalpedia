-- Prove2me | Theorems.Thm_VapnikChervonenkis_Entropy_necessity_step1
-- name    : VapnikChervonenkis.Entropy.necessity_step1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T01:09:08.883846+00:00
-- url     : https://prove2.me/theorems/7241c19d-f7e9-4878-a374-d824fa60a7f4
-- title:
--   Step 1° of necessity — 1 − P(C′) ≥ (1 − P(Q))²
-- statement:
--   Let $(X, P)$ be a probability space and $S$ a collection of subsets of $X$ such that $\pi^{(l)}$ is a measurable function of the sample for every $l$. Let $\varepsilon > 0$ and $l \ge 0$. Consider the events
--
--   $$
--   Q = \Bigl\{\sup_{A \in S} |\nu_A^{(l)} - P_A| > \varepsilon\Bigr\}, \qquad C' = \Bigl\{\sup_{A \in S} |\nu'_A - \nu''_A| > 2\varepsilon\Bigr\},
--   $$
--
--   the first on independent samples of size $l$, the second on independent samples of size $2l$ split into two semi-samples with relative frequencies $\nu'_A$, $\nu''_A$. Then
--
--   $$
--   1 - \mathbf{P}(C') \ge \bigl(1 - \mathbf{P}(Q)\bigr)^2, \qquad\text{i.e.}\qquad \mathbf{P}(C') \le 2\mathbf{P}(Q) - \mathbf{P}^2(Q) .
--   $$
--
--   If $Q$ fails on both semi-samples then $C'$ fails, and the two semi-samples are independent. The inequality transfers a lower bound on $\mathbf{P}(C')$ to a lower bound on $\mathbf{P}(Q)$; in particular $\mathbf{P}(C') \to 1$ forces $\mathbf{P}(Q) \to 1$.
--
--   **Formalization Note.** The unweakened inequality is stated (the paper then weakens it to $\mathbf{P}(Q) \ge \frac12 \mathbf{P}(C')$); the conclusion $\lim \mathbf{P}(Q) = 1$ of (29) needs the unweakened form. $C'$ uses the strict inequality $> 2\varepsilon$, as in its definition on p. 276. The measurability of $\pi^{(l)}$ is the paper's own assumption (p. 265). Probabilities are real numbers (`Measure.real`).
-- source:
--   Vapnik and Chervonenkis, On the Uniform Convergence of Relative Frequencies of Events to Their Probabilities, Theory Probab. Appl. 16 (1971), pp. 276–277, proof of necessity of Theorem 4, step 1°

import Mathlib
import Definitions.Def_VapnikChervonenkis_Shared_deviation

open MeasureTheory Filter Topology

namespace VapnikChervonenkis.Entropy

/-- Step 1° of the proof of necessity in Theorem 4 (pp. 276–277), unweakened: with
`Q = {π^(l) > ε}` on samples of size `l` and `C′ = {sup_{A∈S} |ν′_A − ν″_A| > 2ε} = {ρ^(l) > 2ε}` on
double samples of size `2l`, independence of the two semi-samples gives
`1 − P(C′) ≥ (1 − P(Q))²`, i.e. `P(C′) ≤ 2P(Q) − P²(Q)`. `hπ` is the paper's assumption
(p. 265) that `π^(l)` is measurable. -/
theorem necessity_step1 {X : Type*} [MeasurableSpace X] (P : Measure X)
    [IsProbabilityMeasure P] (S : Set (Set X))
    (hπ : ∀ l, Measurable (Shared.maxDeviation S P l)) (ε : ℝ) (hε : 0 < ε) (l : ℕ) :
    (1 - (Measure.pi (fun _ : Fin l => P)).real {x | ε < Shared.maxDeviation S P l x}) ^ 2
      ≤ 1 - (Measure.pi (fun _ : Fin (l + l) => P)).real
          {x | 2 * ε < Shared.semiSampleDeviation S l x} := by sorry

end VapnikChervonenkis.Entropy
