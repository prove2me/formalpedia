-- Prove2me | Theorems.Thm_SwapDisk_Main_lemma_A_2
-- name    : SwapDisk.Main.lemma_A_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T22:17:35.652006+00:00
-- url     : https://prove2.me/theorems/a4431389-2048-48c3-8539-732515aac540
-- title:
--   Lemma A.2 — refinement by tags: $R_T\le R^{\mathrm{tag}}_T\le 2T$, unplayed tags contribute zero, and $R_T\le\sum_b R(I_b)$ over partitions
-- statement:
--   Let $J$ be a finite tag set with attached points $x_j\in B^2_2$, let $J_t$ be the realized tags and $x_t=x_{J_t}$, $m_j=\sum_t1\{J_t=j\}$, $G_j=\sum_t1\{J_t=j\}g_t$. Then
--   $$R_T\le R^{\mathrm{tag}}_T:=\sum_{j\in J}\psi_{x_j}(G_j)\le2T ,$$
--   an unplayed tag ($m_j=0$) contributes zero, and for every partition $[T]=I_1\,\dot\cup\cdots\dot\cup\,I_k$, $R_T\le\sum_{b=1}^kR(I_b)$.
--
--   Bounding the tag sum is how the algorithm's guarantee transfers to the physical regret.
--
--   Differences from the source:
--   - generalization: a horizon T ≥ 2 (standing assumption) → every T ∈ ℕ; reason: T ≥ 2 is a special case
--   - generalization: partition [T] = I_1 ∪̇ ⋯ ∪̇ I_k → pairwise disjoint `I : Fin k → Finset (Fin T)` covering every round, empty blocks allowed; reason: a partition into nonempty blocks is a special case; an empty block has R(∅) = 0
--   - encoding: tag set J with attached points x_j and x_t = x_{J_t} → `J` a `Fintype` with decidable equality, `pt : J → Disk`, `tag : Fin T → J`, actions `pt (tag t)`; reason: same objects
-- source:
--   Saravanan, Minimax Realized Full Swap Regret on the Euclidean Disk, STOC 2027 submission (manuscript sha256 e7138cc2…), p. 14, Lemma A.2

import Mathlib
import Definitions.Def_SwapDisk_Main_Regret

namespace SwapDisk.Main

/-- Lemma A.2 (Refinement by tags), p. 14: with tags `J_t` and attached points `x_j`
(`x_t = x_{J_t}`), `R_T ≤ R^tag_T = ∑_j ψ_{x_j}(G_j) ≤ 2T`; an unplayed tag contributes zero; for
every partition of the rounds into blocks `I_1, …, I_k`, `R_T ≤ ∑_b R(I_b)`. -/
theorem lemma_A_2 (T : ℕ) {J : Type} [Fintype J] [DecidableEq J] (pt : J → Disk)
    (tag : Fin T → J) (g : Fin T → Disk) :
    swapRegret (fun t => pt (tag t)) g ≤ tagSum pt tag g ∧
    tagSum pt tag g ≤ 2 * T ∧
    (∀ j, tagCount tag j = 0 → psi (pt j : E2) (tagLoss tag g j) = 0) ∧
    ∀ (k : ℕ) (I : Fin k → Finset (Fin T)), Pairwise (fun a b => Disjoint (I a) (I b)) →
      (∀ t, ∃ b, t ∈ I b) →
      swapRegret (fun t => pt (tag t)) g ≤ ∑ b, blockRegret (fun t => pt (tag t)) g (I b) := by sorry

end SwapDisk.Main
