-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P26_superposition_inner_bound
-- name    : QAlgorithms.Papers.Independent.Support50.P26.superposition_inner_bound
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T21:04:08.208655+00:00
-- url     : https://prove2.me/theorems/9aa42cd1-e774-4bcf-9ca4-3d27dded7395
-- title:
--   Theorem 1: superposition coding inner bound
-- statement:
--   Let $X$ be a finite nonempty input alphabet and let $B_1,B_2$ be finite-dimensional nonzero complex output registers. A classical–quantum broadcast channel is a family of positive trace-one operators $\rho_x^{B_1B_2}$. For each finite nonempty auxiliary alphabet $W$ and probability law $p(w,x)=p_W(w)p_{X|W}(x|w)$, compute the information quantities in bits from
--   $$
--   \theta^{WXB_1B_2}=\sum_{w,x}p(w,x)|w\rangle\langle w|\otimes|x\rangle\langle x|\otimes\rho_x^{B_1B_2}.
--   $$
--   Let $\mathcal S(p)$ consist of the nonnegative rate pairs satisfying
--   $$
--   R_1\le I(X;B_1|W)_\theta,\qquad R_2\le I(W;B_2)_\theta,\qquad R_1+R_2\le I(X;B_1)_\theta.
--   $$
--   Every pair in $\bigcup_{W,p}\mathcal S(p)$ is operationally achievable. Specifically, for every $\epsilon,\delta>0$ there is $N\ge1$ such that for every $n\ge N$ there is a deterministic $n$-use encoder with positive integer message sizes $M_1,M_2$, rates $\log_2(M_i)/n\ge R_i-\delta$, and two separate collective decoding POVMs whose joint error averaged over independent uniform messages is at most $\epsilon$. Moreover, writing $d_i=\dim B_i$,
--   $$
--   \bigcup_{W,p}\mathcal S(p)=\bigcup_{|W|\le\min\{|X|,d_1^2+d_2^2-1\},\,p}\mathcal S(p).
--   $$
--   This gives an inner bound without a degradedness assumption and retains the theorem's auxiliary cardinality conclusion.
-- source:
--   Classical codes for quantum broadcast channels, arXiv:1111.3645v4, PDF p. 3, Theorem 1: superposition coding inner bound (paper seed)

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P26

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Support50.P26

attribute [local instance] Classical.propDecidable Classical.decEq

-- Exact primitives from pinned accepted modules, under the independent-paper override.
-- No coding theorem or other paper's channel model is reused.

open QAlgorithms.Papers.Independent.Information100.P22 (Op quantumMI)

open QAlgorithms.Papers.Independent.Information100.P27 (shannon)

open QAlgorithms.Papers.Independent.Claimed50.P08 (cqBlocks)

open QAlgorithms.Papers.Independent.Dependency50.P47 (Law)

variable {X B1 B2 W U V A B : Type}

variable [Fintype X] [Fintype B1] [Fintype B2] [Fintype W] [Fintype U] [Fintype V]

variable [Fintype A] [Fintype B]

variable [DecidableEq X] [DecidableEq B1] [DecidableEq B2] [DecidableEq W]

variable [DecidableEq U] [DecidableEq V] [DecidableEq A] [DecidableEq B]

/-- Theorem 1, PDF p.3, proved pp.4–7: operational inner inclusion for every finite law,
conjoined with the final sentence's equality of unrestricted and capped auxiliary unions. -/
theorem superposition_inner_bound (C : BroadcastChannel X B1 B2) :
    (superUnion C none ⊆ {r | AverageJointAchievable C r}) ∧
    superUnion C none = superUnion C (some (superCap X B1 B2)) := by sorry

end QAlgorithms.Papers.Independent.Support50.P26

end
