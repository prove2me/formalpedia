-- Prove2me | Theorems.Thm_OutlierAssort_ActiveElim_lemma_2
-- name    : OutlierAssort.ActiveElim.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-23T08:39:07.928343+00:00
-- url     : https://prove2.me/theorems/01aa20d3-c60c-4d38-a4b1-acb1ab0f3441
-- title:
--   Lemma 2, p. 14 — |R(S; v̂) − R(S; v)| ≤ 2Σ_{i∈S}|v̂ᵢ − vᵢ|/(1 + Σ_{i∈S} vᵢ)
-- statement:
--   Let $r_i \in [0,1]$ and $v_i \in [0,1]$ be revenues and utilities of $N$ items, and let $\hat v_i \ge 0$ be estimates of the utilities. Write
--   $$
--   R(S; w) = \frac{\sum_{i\in S} r_i w_i}{1+\sum_{i\in S} w_i}
--   $$
--   for the MNL expected revenue of an assortment $S$ under weights $w$. Then for every assortment $S \subseteq [N]$,
--   $$
--   \big|R(S;\hat v) - R(S; v)\big| \le \frac{2\sum_{i\in S}|\hat v_i - v_i|}{1 + \sum_{i\in S} v_i}.
--   $$
--
--   This deterministic perturbation bound converts errors in the estimated utilities into errors in the estimated revenue of an assortment.
--
--   Differences from the source:
--   - generalization: $|S| \le K$ → any $S \subseteq [N]$; reason: the bound does not involve $K$, and the source's sets are included.
--   - reading: arbitrary $\{\hat v_i\}$ → $\hat v_i \ge 0$; reason: the paper's estimates lie in $[0,1]^N$ (notation list, p. 9), and with arbitrary signs the claim is false ($r = 1$, $v = 0$, $\hat v = -0.9$, $S = \{1\}$: left side $9$, right side $1.8$); the upper bound $\hat v_i \le 1$ is not needed.
-- source:
--   Chen, Krishnamurthy, Wang, Robust Dynamic Assortment Optimization in the Presence of Outlier Customers, arXiv:1910.04183v2, p. 14, Lemma 2; proof pp. ec3–ec4 (PDF 30–31)

import Mathlib
import Definitions.Def_ChoiceCDLP_MNL_mnlObjective
import Definitions.Def_OutlierAssort_ActiveElim_Model

namespace OutlierAssort.ActiveElim

/-- Lemma 2 (p. 14): for every assortment `S` and nonnegative estimates `v̂`,
`|R(S; v̂) − R(S; v)| ≤ 2 ∑_{i ∈ S} |v̂_i − v_i| / (1 + ∑_{i ∈ S} v_i)`. -/
theorem lemma_2 {N : ℕ} (r v vhat : Fin N → ℝ) (hr : ∀ i, r i ∈ Set.Icc (0 : ℝ) 1)
    (hv : ∀ i, v i ∈ Set.Icc (0 : ℝ) 1) (hvhat : ∀ i, 0 ≤ vhat i) (S : Finset (Fin N)) :
    |rev r vhat S - rev r v S| ≤ 2 * (∑ i ∈ S, |vhat i - v i|) / (1 + ∑ i ∈ S, v i) := by sorry

end OutlierAssort.ActiveElim
