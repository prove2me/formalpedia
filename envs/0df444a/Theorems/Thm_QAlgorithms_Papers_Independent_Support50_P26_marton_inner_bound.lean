-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P26_marton_inner_bound
-- name    : QAlgorithms.Papers.Independent.Support50.P26.marton_inner_bound
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T21:05:35.065772+00:00
-- url     : https://prove2.me/theorems/23ef2797-9d09-4ba2-a35b-a0b0397c3c24
-- title:
--   Theorem 3: quantum Marton inner bound without a common message
-- statement:
--   Let $x\mapsto\rho_x^{B_1B_2}$ be a finite classical–quantum broadcast channel, with nonempty input alphabet $X$ and nonzero finite output dimensions. Choose any finite nonempty auxiliary alphabets $U_1,U_2$, any joint probability law $p(u_1,u_2)$, and any deterministic function $f:U_1\times U_2\to X$. Compute the information quantities in bits from the actual state
--   $$
--   \theta^{U_1U_2B_1B_2}=\sum_{u_1,u_2}p(u_1,u_2)|u_1\rangle\langle u_1|\otimes|u_2\rangle\langle u_2|\otimes\rho_{f(u_1,u_2)}^{B_1B_2}.
--   $$
--   Let $\mathcal M(p,f)$ consist of the nonnegative pairs obeying
--   $$
--   R_1\le I(U_1;B_1)_\theta,\quad R_2\le I(U_2;B_2)_\theta,\quad R_1+R_2\le I(U_1;B_1)_\theta+I(U_2;B_2)_\theta-I(U_1;U_2)_\theta.
--   $$
--   Every pair in the unrestricted union of these regions is operationally achievable: for every $\epsilon,\delta>0$, all sufficiently large positive block lengths admit a deterministic code with rates at least $R_i-\delta$ and average joint decoding error at most $\epsilon$, using independent uniform messages and separate collective receiver POVMs. Furthermore,
--   $$
--   \bigcup_{U_1,U_2,p,f}\mathcal M(p,f)=\bigcup_{|U_1|,|U_2|\le |X|,\,p,f}\mathcal M(p,f).
--   $$
--   This is a two-private-message inner bound with a correlation penalty, together with both cardinality conclusions; it is not a capacity equality.
-- source:
--   Classical codes for quantum broadcast channels, arXiv:1111.3645v4, PDF p. 8, Theorem 3: quantum Marton inner bound without a common message

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

/-- Theorem 3, PDF p.8, proved pp.8–14: Marton inner inclusion and both auxiliary
cardinality conclusions, expressed as equality of unions. Only two private messages occur. -/
theorem marton_inner_bound (C : BroadcastChannel X B1 B2) :
    (martonUnion C none ⊆ {r | AverageJointAchievable C r}) ∧
    martonUnion C none = martonUnion C (some (Fintype.card X)) := by sorry

end QAlgorithms.Papers.Independent.Support50.P26

end
