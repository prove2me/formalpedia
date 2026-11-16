-- Prove2me | Theorems.Thm_RandomDimReduction_Channel_Supplement_theorem_3_4
-- name    : RandomDimReduction.Channel.Supplement.theorem_3_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T21:44:50.797528+00:00
-- url     : https://prove2.me/theorems/36f18269-be37-4a05-8d18-c3dd5c5624d8
-- title:
--   Theorem 3.4 — no random joint purification channel
-- statement:
--   For every $d\ge2$, $n\ge1$ and $2\le k\le d$, put $H_{data}=(\mathbb C^d)^{\otimes n}\otimes(\mathbb C^d)^{\otimes n}$ and $H_{purify}=(\mathbb C^k)^{\otimes n}\otimes(\mathbb C^k)^{\otimes n}$. There is no complex-linear CPTP map $P:L(H_{data})\to L(H_{data}\otimes H_{purify})$ such that every four density operators $\rho,\sigma,\widetilde\rho,\widetilde\sigma$ with a common isometry $W:\mathbb C^k\to\mathbb C^d$ satisfying $W\widetilde\rho W^\dagger=\rho$ and $W\widetilde\sigma W^\dagger=\sigma$ admit a Borel probability measure $\nu$ on $U(k)$ with both
--   $$\operatorname{tr}_{purify}P(\rho^{\otimes n}\otimes\sigma^{\otimes n})=\rho^{\otimes n}\otimes\sigma^{\otimes n}$$
--   and
--   $$\operatorname{tr}_{data}P(\rho^{\otimes n}\otimes\sigma^{\otimes n})=\int (U\widetilde\rho U^\dagger)^{\otimes n}\otimes(U\widetilde\sigma U^\dagger)^{\otimes n}\,d\nu(U).$$
--   The law can depend on the input tuple; within a sample the same unitary acts everywhere. No rank-sum promise is imposed. This separates simultaneous dimension reduction from the proposed two-state random purification property.
--
--   Differences from the source:
--   - encoding: a quantum channel on density operators → a complex-linear CPTP map on the entire operator algebra; reason: the state-domain notation denotes a genuine quantum channel extension
--   - encoding: for every compatible tuple there is a probability measure on U(k) → for every four density matrices and common isometry there exists a Borel probability measure satisfying both marginal equations; reason: the unitary group carries its usual Borel structure, and the law may vary with the tuple
-- source:
--   Angus Lowe, Xinyu Tan, Random dimension reduction and learning symmetric properties of quantum states, STOC 2027 submission #994 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/994.pdf, Theorem 3.4, p. 11

import Definitions.Def_RandomDimReduction_Channel_Supplement_Joint

set_option autoImplicit false
noncomputable section

namespace RandomDimReduction.Channel.Supplement

/-- Theorem 3.4, pp.11–12: no fixed CPTP extension satisfies both marginal equations
for every compatible input, even with a separate arbitrary probability measure per tuple. -/
theorem theorem_3_4 (d n k : ℕ) (hd : 2 ≤ d) (hn : 0 < n) (hk : 2 ≤ k) (hkd : k ≤ d) :
    ¬ ∃ P : Op (Data n d) →ₗ[ℂ] Op (Data n d × Purify n k),
      WildeQIT.EntBreaking.IsQuantumChannel P ∧ JointMarginals n k d P := by sorry

end RandomDimReduction.Channel.Supplement
