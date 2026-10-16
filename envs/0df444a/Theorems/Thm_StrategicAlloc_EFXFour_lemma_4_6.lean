-- Prove2me | Theorems.Thm_StrategicAlloc_EFXFour_lemma_4_6
-- name    : StrategicAlloc.EFXFour.lemma_4_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T14:14:49.361027+00:00
-- url     : https://prove2.me/theorems/a311059b-7759-480a-9e59-bc254c940ade
-- title:
--   Lemma 4.6 — v_1({h_1, h_4}) ≥ µ_1 and max{v_1({h_1}), v_1({h_2, h_3})} ≥ µ_1 for four sorted positive goods
-- statement:
--   Consider two agents and four goods with additive non-negative valuations, and name the goods $h_1, h_2, h_3, h_4$ so that agent 1's values are sorted and all positive:
--   $$
--   v_1(h_1) \ge v_1(h_2) \ge v_1(h_3) \ge v_1(h_4) > 0.
--   $$
--   Then the maximin share $\mu_1$ of agent 1 satisfies
--   $$
--   v_1(\{h_1, h_4\}) \ge \mu_1 \qquad\text{and}\qquad \max\{v_1(\{h_1\}),\ v_1(\{h_2, h_3\})\} \ge \mu_1.
--   $$
--
--   The paper attributes the lemma to the proof of Theorem 5.1 of Amanatidis, Birmpas and Markakis, *On truthful mechanisms for maximin share allocations* (IJCAI 2016). In the proof of Theorem 4.5 it identifies three bundles that always guarantee agent 1 her maximin share, which reduces the possible bundles of an agent who misses it to a short list.
--
--   **Formalization Note** The renaming of the goods is a bijection $h$ of `Fin 4`, with $h_j$ = `h (j - 1)`. The page writes $v_i$ in the conclusion; the context ("$v_1$ as above") makes clear that $v_1$ is meant, and the Lean states it for agent 1 (`0`).
-- source:
--   Amanatidis et al., Allocating Indivisible Goods to Strategic Agents, arXiv:2109.08644v2, p. 19, Lemma 4.6 (renaming h_1, …, h_4 from the proof of Theorem 4.5, p. 19)

import Mathlib
import Definitions.Def_StrategicAlloc_EFXFour_Setting

namespace StrategicAlloc.EFXFour

theorem lemma_4_6 (v : Fin 2 → Fin 4 → ℝ) (hv : ∀ i g, 0 ≤ v i g) (h : Fin 4 ≃ Fin 4)
    (h01 : v 0 (h 1) ≤ v 0 (h 0)) (h12 : v 0 (h 2) ≤ v 0 (h 1)) (h23 : v 0 (h 3) ≤ v 0 (h 2))
    (h3pos : 0 < v 0 (h 3)) :
    mu v 0 ≤ StrategicAlloc.RRFair.val v 0 {h 0, h 3} ∧ mu v 0 ≤ max (StrategicAlloc.RRFair.val v 0 {h 0}) (StrategicAlloc.RRFair.val v 0 {h 1, h 2}) := by sorry

end StrategicAlloc.EFXFour
