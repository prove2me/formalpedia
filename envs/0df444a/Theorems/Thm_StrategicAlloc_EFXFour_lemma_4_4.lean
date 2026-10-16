-- Prove2me | Theorems.Thm_StrategicAlloc_EFXFour_lemma_4_4
-- name    : StrategicAlloc.EFXFour.lemma_4_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T14:14:48.772788+00:00
-- url     : https://prove2.me/theorems/e8f6727a-4d41-464d-9775-b2a07a8c600b
-- title:
--   Lemma 4.4 — with at most three positively valued goods, EFX from one's own view gives µ_i (2 agents, 4 goods)
-- statement:
--   Consider two agents and four goods, with additive non-negative valuations $v_1, v_2$, and let $\mu_i$ be the maximin share of agent $i$. Fix an agent $i \in \{1, 2\}$ and suppose that $i$ has strictly positive value for at most three of the four goods:
--   $$
--   \bigl|\{ g \in M : v_i(g) > 0 \}\bigr| \le 3.
--   $$
--   Then in every allocation $(A_1, A_2)$ which is EFX from the point of view of agent $i$, agent $i$ receives at least her maximin share:
--   $$
--   v_i(A_i) \ge \mu_i.
--   $$
--
--   The lemma disposes of the degenerate instances in the proof of Theorem 4.5: once it is known, a counterexample to Theorem 4.5 must have all four goods positively valued by the agent who misses her maximin share.
--
--   **Formalization Note** Agents are `Fin 2`, goods `Fin 4`. "EFX from her point of view" is the EFX condition of Definition 2.1 with the envying agent fixed to $i$; the allocation is required to be a partition of the goods.
-- source:
--   Amanatidis et al., Allocating Indivisible Goods to Strategic Agents, arXiv:2109.08644v2, p. 19, Lemma 4.4

import Mathlib
import Definitions.Def_StrategicAlloc_EFXFour_Setting

namespace StrategicAlloc.EFXFour

theorem lemma_4_4 (v : Fin 2 → Fin 4 → ℝ) (hv : ∀ i g, 0 ≤ v i g) (i : Fin 2)
    (hpos : (Finset.univ.filter (fun g => 0 < v i g)).card ≤ 3)
    (A : Fin 2 → Finset (Fin 4)) (hA : StrategicAlloc.RRFair.IsAllocation A) (hEFX : IsEFXFor v A i) :
    mu v i ≤ StrategicAlloc.RRFair.val v i (A i) := by sorry

end StrategicAlloc.EFXFour
