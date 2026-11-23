-- Prove2me | Theorems.Thm_QMA2ClassicalSep_Main_bgh_product_overlap
-- name    : QMA2ClassicalSep.Main.bgh_product_overlap
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T03:36:52.954032+00:00
-- url     : https://prove2.me/theorems/8f4b27d6-2958-409c-af64-c899a9a85e8d
-- title:
--   Product-state overlap with the four-party antisymmetric projector is at most $1/3$
-- statement:
--   For every $N$ and every pair of normalized vectors $\alpha,\beta\in\mathbb C^{[N]\times[N]}$, the product vector $\alpha\otimes\beta$ on the grouping $((A_1A_2),(B_1B_2))$ satisfies
--   $$
--   \langle\alpha\otimes\beta|P_N|\alpha\otimes\beta\rangle\le \frac13,
--   $$
--   where $P_N=\sum_{|Q|=4}|\operatorname{Alt}_Q\rangle\langle\operatorname{Alt}_Q|$ is the projector onto the four-party antisymmetric subspace. The proposition includes $N<4$, when $P_N=0$.
--
--   A proof can follow the exchange calculation in [BGH+26, Lemma 4.1]: project each factor to its antisymmetric part within its two parties, expand the six cosets of $S_2\times S_2$ in $S_4$, bound the full-exchange term by $|\langle\alpha,\beta\rangle|^2\le\|\alpha\|^2\|\beta\|^2$, and discard the two nonnegative Gram-trace terms.
-- source:
--   Paper p.21, Eq.(3), invoking [BGH+26, Lemma 4.1]. This is the normalized-product expectation formulation whose supremum is the paper's h_Sep(P_N).

import Definitions.Def_QMA2ClassicalSep_Main_HardDist

open scoped BigOperators ComplexConjugate
open Matrix

theorem QMA2ClassicalSep.Main.bgh_product_overlap (N : ℕ) (α β : Fin N × Fin N → ℂ) :
    QMA2ClassicalSep.Main.IsUnit' α → QMA2ClassicalSep.Main.IsUnit' β →
      QMA2ClassicalSep.Main.expect (QMA2ClassicalSep.Main.projAlt N)
        (fun i => α i.1 * β i.2) ≤ 1 / 3 := by sorry
