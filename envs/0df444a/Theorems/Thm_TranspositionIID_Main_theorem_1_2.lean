-- Prove2me | Theorems.Thm_TranspositionIID_Main_theorem_1_2
-- name    : TranspositionIID.Main.theorem_1_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:22:18.236925+00:00
-- url     : https://prove2.me/theorems/91b86e6c-7d70-416a-9ede-5cb9304ee0f3
-- title:
--   Theorem 1.2 — expected cost at most OPT plus 1250
-- statement:
--   For every $n\ge1$, every probability vector $p$ on $n$ labels, every initial list $\sigma_0$, and every integer $t\ge n^{29}$, the transposition rule satisfies
--   $$\mathbb E[\operatorname{Cost}_p(\sigma_t)]\le\operatorname{OPT}_p+1250.$$
--   The list $\sigma_t$ is the state after exactly $t$ independent request updates. The expectation is the next-query cost, and the conclusion includes zero probabilities, ties and all later times. This is the paper's uniform finite-time main result.
--
--   Differences from the source:
--   - encoding: labels and charged positions 1 through n → labels and positions Fin n with charged position val + 1; reason: the order-preserving shift gives a bijection of all labels and list states
--   - encoding: decreasing relabeling with OPT equal to the sorted positional cost → OPT is the attained minimum over all permutations; reason: sorting shows these are identical, including ties and zeros; no label order is required by the goal
--   - encoding: IID requests and the state after t steps → the explicit request kernel raised to the natural power t; reason: finite matrix products give exactly the IID marginal law; nonnegative integer times are Nat
-- source:
--   Clayton Mizgerd, Transposition achieves OPT+O(1) in polynomial time for IID list update, STOC 2027 submission #668 (October 2026), supplied canonical submission artifact; citation basis published (not acceptance). Theorem 1.2, printed p.2 = PDF p.2; source.pdf SHA256 07dbf227a79b9907070bc1c27f25a0848cee3135ec65bcf105159f991b3b4545.

import Definitions.Def_TranspositionIID_Main_ListModel

namespace TranspositionIID.Main

/-- Theorem 1.2, printed/PDF p.2: exact exponent 29, constant 1250, and all later times. -/
theorem theorem_1_2 {n : ℕ} (hn : 1 ≤ n) (p : Fin n → ℝ)
    (hp : ActuarialValuation.isFiniteStateDistribution p)
    (σ₀ : ListState n) (t : ℕ) (ht : n ^ 29 ≤ t) :
    expectedAfter (transpositionKernel p) σ₀ t (cost p) ≤ optimum p + 1250 := by sorry

end TranspositionIID.Main
