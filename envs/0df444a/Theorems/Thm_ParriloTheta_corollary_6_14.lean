-- Prove2me | Theorems.Thm_ParriloTheta_corollary_6_14
-- name    : ParriloTheta.corollary_6_14
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:31:05.020411+00:00
-- url     : https://prove2.me/theorems/0f135410-54bd-452a-94af-3f3a4ef5c401
-- title:
--   Corollary 6.14 — $\vartheta\text{-rank}(C_{2n+1}\oplus\overline{K_m})=1$ iff $m\le4+\frac4{n-1}$; $\vartheta\text{-rank}(\overline{C_{2n+1}}\oplus\overline{K_m})=1$ iff $m\le8$
-- statement:
--   Let $n\ge2$ and $m\ge0$ be integers. Let $C_{2n+1}$ be the cycle on $2n+1$ nodes, $\overline{C_{2n+1}}$ its complement, and $\overline{K_m}$ the graph on $m$ nodes with no edges; $\oplus$ is the disjoint union. Then
--   1. $\vartheta\text{-rank}(C_{2n+1}\oplus\overline{K_m})=1$ if and only if $m\le 4+\dfrac{4}{n-1}$;
--   2. $\vartheta\text{-rank}(\overline{C_{2n+1}}\oplus\overline{K_m})=1$ if and only if $m\le8$.
--
--   For example $C_5\oplus\overline{K_8}$ has $\vartheta$-rank $1$ while $C_5\oplus\overline{K_9}$ does not, so adding an isolated node can increase the $\vartheta$-rank. This refutes the conjecture of Gvozdenović and Laurent that adding isolated nodes never increases the $\vartheta$-rank.
--
--   **Formalization Note** $C_{2n+1}$ is `cycleGraph (2 * n + 1)`, $\overline{K_m}$ is `(⊥ : SimpleGraph (Fin m))`, $\oplus$ is `⊕g`. The $\vartheta$-rank is `ℕ∞`-valued and the threshold $4+4/(n-1)$ is computed in $\mathbb R$. The case $m=0$ is included.
--
--   Differences from the source:
--   - encoding: C_{2n+1}, C̄_{2n+1}, K̄_m, ⊕ → cycleGraph (2 * n + 1), its complement ᶜ, (⊥ : SimpleGraph (Fin m)), ⊕g; reason: K̄_m is m isolated nodes; Lean convention, same graphs
--   - encoding: m ≤ 4 + 4/(n−1) → (m : ℝ) ≤ 4 + 4 / ((n : ℝ) − 1); reason: real arithmetic; same threshold
--   - encoding: ϑ-rank(G) ∈ ℕ ∪ {∞} → thetaRank G : ℕ∞ (⊤ = ∞); reason: Lean convention; same values
-- source:
--   Laurent & Vargas, Exactness of Parrilo's conic approximations for copositive matrices and associated low order bounds for the stability number of a graph, arXiv:2109.12876v1, Corollary 6.14, p.24

import Mathlib
import Definitions.Def_ParriloTheta_thetaRank

namespace ParriloTheta

open SimpleGraph

/-- **Corollary 6.14: how many isolated nodes keep ϑ-rank 1 for odd cycles and their
complements.**
Laurent & Vargas, *Exactness of Parrilo's conic approximations for copositive matrices and
associated low order bounds for the stability number of a graph*, arXiv:2109.12876v1, Corollary 6.14, p.24:
"For any integer n ≥ 2 the following holds:
(i) ϑ-rank(C2n+1 ⊕ K̄m) = 1 if and only if m ≤ 4 + 4/(n−1).
(ii) ϑ-rank(C̄2n+1 ⊕ K̄m) = 1 if and only if m ≤ 8."

**Formalization Note.** `C_{2n+1}` is `cycleGraph (2 * n + 1)` on `Fin (2n+1)` and `C̄_{2n+1}`
its complement `ᶜ`; `K̄_m` (overline: the complement of the complete graph) is `m` isolated
nodes, `(⊥ : SimpleGraph (Fin m))`; `⊕` is the disjoint union `⊕g`. Every `m : ℕ` is allowed
(`m = 0` is the bare graph). ϑ-rank is `ℕ∞`-valued; the threshold `4 + 4/(n − 1)` is computed
in `ℝ`. -/
theorem corollary_6_14 (n m : ℕ) (hn : 2 ≤ n) :
    (thetaRank (cycleGraph (2 * n + 1) ⊕g (⊥ : SimpleGraph (Fin m))) = 1 ↔
      (m : ℝ) ≤ 4 + 4 / ((n : ℝ) - 1)) ∧
    (thetaRank ((cycleGraph (2 * n + 1))ᶜ ⊕g (⊥ : SimpleGraph (Fin m))) = 1 ↔ m ≤ 8) := by sorry

end ParriloTheta
