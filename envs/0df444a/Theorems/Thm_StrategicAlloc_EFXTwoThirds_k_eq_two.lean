-- Prove2me | Theorems.Thm_StrategicAlloc_EFXTwoThirds_k_eq_two
-- name    : StrategicAlloc.EFXTwoThirds.k_eq_two
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T15:58:39.901227+00:00
-- url     : https://prove2.me/theorems/b5c62fa9-ee28-44b7-957f-900869f7ded1
-- title:
--   Proof of Theorem 4.7, p. 21 — an EFX allocation giving agent i at most 2µ_i/3 leaves exactly two positive goods to the other agent
-- statement:
--   Let two agents have additive non-negative valuations over a finite set $M$ of goods, and let $(A_1,A_2)$ be an EFX allocation. Let $i$ be an agent with maximin share $\mu_i>0$ and $v_i(A_i)\le \tfrac23\mu_i$, and let $j\ne i$ be the other agent. Write $S=\{g\in A_j: v_i(g)>0\}$. Then
--
--   $$|S|=2,\qquad v_i(A_j)=\tfrac43\,\mu_i,\qquad v_i(g)=\tfrac23\,\mu_i\ \text{ for each } g\in S.$$
--
--   This is the first step of the proof of Theorem 4.7: an EFX allocation that is no better than $\tfrac23$-MMS for some agent must have a very rigid shape.
--
--   **Formalization Note** The page states the claim for agent 1 after a "without loss of generality"; the statement is posed for an arbitrary agent $i$ and the other agent $j$. The hypotheses $\mu_i>0$ and $v_i(A_i)\le\tfrac23\mu_i$ are the proof's context (p. 20: the negation of the theorem at agent $i$); the page then notes $v_i(A_i)=\tfrac23\mu_i$ by Theorem 2.6.
-- source:
--   Amanatidis et al., Allocating Indivisible Goods to Strategic Agents, arXiv:2109.08644v2, pp. 20–21, §4.2, proof of Theorem 4.7, last paragraph of p. 20 and first paragraph of p. 21

import Mathlib
import Definitions.Def_StrategicAlloc_EFXTwoThirds_Setting

namespace StrategicAlloc.EFXTwoThirds

/-- Proof of Theorem 4.7 (p. 21, first paragraph): if an EFX allocation gives agent `i` at most
`2µ_i/3` and `µ_i > 0`, then the other agent's bundle `A_j` contains exactly two goods of positive
value to `i`, `v_i(A_j) = 4µ_i/3`, and each of these two goods is worth `2µ_i/3` to `i`. -/
theorem k_eq_two {m : ℕ} (v : Fin 2 → Fin m → ℝ) (hv : ∀ i g, 0 ≤ v i g)
    (A : Fin 2 → Finset (Fin m)) (hA : IsAllocation A) (hEFX : IsEFX v A)
    (i j : Fin 2) (hij : i ≠ j) (hmu : 0 < StrategicAlloc.EFXFour.mu v i)
    (hle : val v i (A i) ≤ 2 / 3 * StrategicAlloc.EFXFour.mu v i) :
    ((A j).filter (fun g => 0 < v i g)).card = 2 ∧
      val v i (A j) = 4 / 3 * StrategicAlloc.EFXFour.mu v i ∧
      ∀ g ∈ (A j).filter (fun g => 0 < v i g), v i g = 2 / 3 * StrategicAlloc.EFXFour.mu v i := by sorry

end StrategicAlloc.EFXTwoThirds
