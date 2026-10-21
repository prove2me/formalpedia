-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P02_majority_vote_three_inputs
-- name    : QAlgorithms.Papers.Independent.Claimed50.P02.majority_vote_three_inputs
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T08:33:08.059661+00:00
-- url     : https://prove2.me/theorems/067cb823-3a0c-4466-88d1-f3e82f471af8
-- title:
--   §7.2, unnumbered: optimal three-input majority fidelity is 8/9
-- statement:
--   Let $d\ge2$. For a string $x\in[d]^3$, let $f(x)$ contain every symbol of maximal frequency in $x$, and let $\Pi_{f(x)}=\sum_{a\in f(x)}|a\rangle\langle a|$. Among all CPTP unitary-equivariant three-input, one-output qudit channels, the attained optimal worst-case fidelity is
--   $$
--   \max_{\Phi}\ \min_{x\in[d]^3}\operatorname{Tr}\!\left(\Phi(|x\rangle\langle x|)\Pi_{f(x)}\right)=\frac89.
--   $$
--   Both existence of a channel achieving this guarantee and the upper bound for every such channel are included. The projector is not divided by the number of valid outputs. At $d=2$ no all-distinct input exists. This extends the binary result to every local dimension.
-- source:
--   Linear programming with unitary-equivariant constraints, arXiv:2207.05713v2, PDF p. 42, §7.2, unnumbered: optimal three-input majority fidelity is 8/9

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P02

namespace QAlgorithms.Papers.Independent.Claimed50.P02

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

open QAlgorithms.Papers.Independent.Information100.P69 (Sites choi)

noncomputable section

/-- Paper p.42, §7.2: exact optimal three-input majority fidelity, with
attainment and the upper bound over every equivariant CPTP channel.
At d=2 the all-distinct orbit is automatically absent. -/
theorem majority_vote_three_inputs {d : ℕ} (hd : 2 ≤ d) :
    IsGreatest {F : ℝ | ∃ Phi : Superop (Sites (Fin d) 3) (Sites (Fin d) 1),
      IsChannel Phi ∧ UnitaryEquivariant Phi ∧ ∀ x, F ≤ majoritySuccess Phi x}
      (8/9 : ℝ) := by sorry

end

end QAlgorithms.Papers.Independent.Claimed50.P02
