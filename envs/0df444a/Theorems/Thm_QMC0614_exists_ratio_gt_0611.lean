-- Prove2me | Theorems.Thm_QMC0614_exists_ratio_gt_0611
-- name    : QMC0614.exists_ratio_gt_0611
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-02T21:42:30.318207+00:00
-- url     : https://prove2.me/theorems/7678556d-87cc-480c-822f-9faeafd8508a
-- title:
--   ALMPS25 Eq. (19) in max form at $d=14/15$: ratio $>0.611$ on every edge
-- statement:
--   **The $0.611$ quantum max-cut endgame in max form** (ALMPS25, arXiv:2504.15276, Section 4.2, Eq. (19)).
--
--   For one edge of a quantum max-cut instance in the level-13 Pauli relaxation, let
--   $s=\tfrac13\operatorname{Tr}[(X_iX_j+Y_iY_j+Z_iZ_j)\rho]$ be its Pauli correlation (so $\tfrac12(1-3s)$ is the
--   SDP bound on the edge's contribution). The MATCH and PMATCH rounding strategies have per-edge ratios
--   $$E_M(s)=\frac{1+3d\,[-\tfrac{1+3s}{2}]^{+}}{1-3s},\qquad
--   E_{PM}(\sigma,s)=\frac{1-F(s)(1-\sigma^{2})+d\,\sigma\bigl(1-F(s)(1+\sigma)\bigr)[-\tfrac{1+3s}{2}]^{+}}{1-3s},$$
--   with $\sigma=\sin\theta$, $F$ the BFV product expectation and $[x]^{+}=\max\{x,0\}$.
--
--   **Theorem.** There exist $\mu\in[0,1]$ and $\sigma\in[0,1]$ — explicitly $\mu=0.861$,
--   $\sigma=0.28086$ ($\theta\approx0.2847$) — with
--   $$\forall s\in[-1,\tfrac13):\quad 0.611<\mu\,E_{PM}(\sigma,s)+(1-\mu)\,E_M(s)$$
--   at $d=14/15$, the matching weight of the augmented second-level SDP with a separation oracle.
--
--   This is the max form of the paper's Eq. (19): the inner minimum over $s$ of the mixture at one admissible
--   parameter pair exceeds $0.611$, so the max-min value — and hence the approximation ratio of "better of MATCH and
--   PMATCH" — does too. The proof is a single instantiation of the pointwise per-edge theorem
--   (`QMC0614.ratio_gt_0611`, already proved on the platform), which is why this node is recorded as a reduction: the
--   mathematical content (three series bounds on $F$ plus exact Bernstein certificates for a quartic) lives there.
-- source:
--   Anshu, Lee, Mousavi, Parekh, Soleimanifar, arXiv:2504.15276 (ESA 2025), Section 4.2 Eq. (19) with the certified point (d=14/15, theta=0.2847, mu=0.861), level k=13.

import Mathlib
import Definitions.Def_QuantumMaxCutBFVProductRounding
open scoped BigOperators

namespace QMC0614

theorem exists_ratio_gt_0611 :
    ∃ μ σ : ℝ, 0 ≤ μ ∧ μ ≤ 1 ∧ 0 ≤ σ ∧ σ ≤ 1 ∧
      ∀ s : ℝ, -1 ≤ s → s < 1 / 3 → (0.611 : ℝ) < mixture (14 / 15) μ σ s := by sorry

end QMC0614
