-- Prove2me | Theorems.Thm_WalledBrauer_Blocks_lemma_4_1
-- name    : WalledBrauer.Blocks.lemma_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T13:44:51.466888+00:00
-- url     : https://prove2.me/theorems/70e2b009-dabd-471a-8cc9-3348a00c0990
-- title:
--   Lemma 4.1 — action of $T_{r,s}=\sum E_{i,j}$ on cell modules
-- statement:
--   Let $k$ be an algebraically closed field of characteristic $0$, $\delta\in k$, and $(\lambda^L,\lambda^R)\in\Lambda^{r-t,s-t}$. Put
--   $$
--   T_{r,s}=\sum_{1\le i\le r<j\le r+s}E_{i,j}\in B_{r,s}(\delta).
--   $$
--   Then for every $y\in\Delta_{r,s}(\lambda^L,\lambda^R)$,
--   $$
--   T_{r,s}\,y=\Big(t\delta-\sum_{d\in[\lambda^L]}c(d)-\sum_{d\in[\lambda^R]}c(d)+\sum_{1\le i<m\le r}(i,m)+\sum_{r<i<m\le r+s}(i,m)\Big)y ,
--   $$
--   where $(i,m)\in\Sigma_{r,s}$ is the transposition of $i$ and $m$, and $c(d)$ is the content of the box $d$.
--
--   This computes the action of a quasi-central element on every cell module. It is the source of the content condition on blocks (Theorem 4.2, Corollary 4.3).
--
--   **Formalization Note** The scalar enters through `algebraMap k`. The sums run over 0-based nodes: $i<r\le j$ for $T_{r,s}$, and $i<m$ both $<r$ or both $\ge r$ for the transpositions. The paper proves the lemma for every field; it is posed here in characteristic $0$ because the cell modules are modelled with Young symmetrizers.
-- source:
--   Cox, De Visscher, Doty & Martin, On the blocks of the walled Brauer algebra, arXiv:0709.0851v1, p. 17, Lemma 4.1

import Mathlib
import Definitions.Def_WalledBrauer_Blocks_CellModules
import Definitions.Def_WalledBrauer_Blocks_Partitions

namespace WalledBrauer.Blocks

/-- Lemma 4.1 (p. 17). For `(λL, λR) ∈ Λ^{r-t,s-t}` and every `y ∈ Δ_{r,s}(λL, λR)`,
`T_{r,s} y = (tδ - ∑_{d ∈ [λL]} c(d) - ∑_{d ∈ [λR]} c(d) + ∑_{1 ≤ i < m ≤ r} (i, m)
+ ∑_{r < i < m ≤ r+s} (i, m)) y`, where `T_{r,s} = ∑_{1 ≤ i ≤ r < j ≤ r+s} E_{i,j}`. -/
theorem lemma_4_1 {k : Type*} [Field k] [CharZero k] [IsAlgClosed k] {r s : ℕ} (δ : k)
    (x : CellIndex r s) (y : CellModule δ x) :
    (∑ i : Fin (r + s), ∑ j : Fin (r + s),
        if i.val < r ∧ r ≤ j.val then diag (δ := δ) (WalledDiagram.E i j) else 0) • y =
      (algebraMap k (WalledBrauerAlgebra k r s δ)
          ((x.t : k) * δ - (totalContent x.L : k) - (totalContent x.R : k)) +
        ∑ i : Fin (r + s), ∑ m : Fin (r + s),
          if i < m ∧ (m.val < r ∨ r ≤ i.val) then
            diag (δ := δ) (WalledDiagram.perm (Equiv.swap i m))
          else 0) • y := by sorry

end WalledBrauer.Blocks
