-- Prove2me | Theorems.Thm_StrategicAlloc_EFXTwoThirds_two_pos_goods_own
-- name    : StrategicAlloc.EFXTwoThirds.two_pos_goods_own
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T15:58:22.301811+00:00
-- url     : https://prove2.me/theorems/399a7c58-b6c2-4f47-9722-44301f15c9b5
-- title:
--   Proof of Theorem 4.7, p. 21 — under the same hypotheses agent i's own bundle has at least two positive goods
-- statement:
--   Let two agents have additive non-negative valuations over a finite set $M$ of goods, and let $(A_1,A_2)$ be an EFX allocation. If agent $i$ has maximin share $\mu_i>0$ and $v_i(A_i)\le\tfrac23\mu_i$, then
--
--   $$\bigl|\{g\in A_i : v_i(g)>0\}\bigr|\ \ge\ 2 .$$
--
--   This is the second step of the proof of Theorem 4.7; it supplies the goods $h_3,h_4$ on which the auxiliary instance $v^*$ is built.
--
--   **Formalization Note** As for the previous step, the page argues for agent 1 after a "without loss of generality"; the statement is posed for an arbitrary agent $i$, with the proof's context $\mu_i>0$ and $v_i(A_i)\le\tfrac23\mu_i$ as hypotheses.
-- source:
--   Amanatidis et al., Allocating Indivisible Goods to Strategic Agents, arXiv:2109.08644v2, p. 21, §4.2, proof of Theorem 4.7, second paragraph

import Mathlib
import Definitions.Def_StrategicAlloc_EFXTwoThirds_Setting

namespace StrategicAlloc.EFXTwoThirds

/-- Proof of Theorem 4.7 (p. 21, second paragraph): under the hypotheses of `k_eq_two`, agent
`i`'s own bundle `A_i` contains at least two goods of positive value to `i`. -/
theorem two_pos_goods_own {m : ℕ} (v : Fin 2 → Fin m → ℝ) (hv : ∀ i g, 0 ≤ v i g)
    (A : Fin 2 → Finset (Fin m)) (hA : IsAllocation A) (hEFX : IsEFX v A)
    (i : Fin 2) (hmu : 0 < StrategicAlloc.EFXFour.mu v i)
    (hle : val v i (A i) ≤ 2 / 3 * StrategicAlloc.EFXFour.mu v i) :
    2 ≤ ((A i).filter (fun g => 0 < v i g)).card := by sorry

end StrategicAlloc.EFXTwoThirds
