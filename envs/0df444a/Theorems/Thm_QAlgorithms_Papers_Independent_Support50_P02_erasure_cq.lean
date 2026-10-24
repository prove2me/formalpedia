-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P02_erasure_cq
-- name    : QAlgorithms.Papers.Independent.Support50.P02.erasure_cq
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T18:17:38.135315+00:00
-- url     : https://prove2.me/theorems/1a175037-b8f6-4b2a-a0e5-0a29dfbc8c91
-- title:
--   §7.1: controlled erasure MAC cq capacity
-- statement:
--   Let $d\ge1$. Alice has a qubit, Bob a $d$-dimensional register, and Charlie a $d+1$-dimensional register with an orthogonal erasure flag $|e\rangle$. The controlled-erasure MAC measures Alice in the computational basis: outcome $0$ discards Bob's input and outputs the flag; outcome $1$ transfers Bob's input coherently to the nonflag subspace. Thus, for density operators $\tau,\rho$,
--   $$\mathcal E_d(\tau\otimes\rho)=\tau_{00}|e\rangle\langle e|+\tau_{11}\rho.$$
--   With nonnegative cq operational rates, squared joint fidelity, and entropy in bits,
--   $$CQ(\mathcal E_d)=\{(r,S)\ge0:\exists q\in[0,1/2],\ r\le H_2(q),\ S\le(1-2q)\log_2d\}=CQ^{(1)}(\mathcal E_d).$$
--   Here $H_2$ is binary entropy and the single-letter region uses non-strict boundaries. This is the complete capacity equality, not just an achievable Bell-input point.
--
--   **Formalization Note** The printed Kraus family on p.32 is corrected to agree with the prose and displayed product-input action; transfer coherences are preserved.
-- source:
--   Capacity Theorems for Quantum Multiple Access Channels: Classical-Quantum and Quantum-Quantum Capacity Regions, arXiv:quant-ph/0501045v3, PDF p. 8, §7.1: controlled erasure MAC cq capacity

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P02

noncomputable section

open scoped BigOperators Matrix ComplexConjugate

namespace QAlgorithms.Papers.Independent.Support50.P02

open QAlgorithms.Papers.Independent.Information100.P67
  (squaredFidelity receiverChannel complementaryChannel IsDegradable)

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Information100.P03 (PureEnsemble)

open QAlgorithms.Papers.Independent.Dependency50.P19 (epr)

attribute [local instance] Classical.propDecidable Classical.decEq

variable {A B C E R S I J : Type*}

variable [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

variable [Fintype C] [DecidableEq C] [Fintype E] [DecidableEq E]

variable [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S]

variable [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

/-- Boundary-inclusive erasure cq formula, PDF p.8 and §7.1 pp.32–33.
The channel follows the corrected prose-defined Kraus family, not the erroneous
printed family. At d=1 this still includes the full classical bit interval. -/
theorem erasure_cq (d : ℕ) (hd : 0 < d) :
    cqMacCapacity (controlledErasure d) =
      {r | Nonnegative r ∧ ∃ q : ℝ, 0 ≤ q ∧ q ≤ 1 / 2 ∧
        r.1 ≤ binEntropy2 q ∧ r.2 ≤ (1 - 2 * q) * Real.logb 2 d} ∧
    cqMacCapacity (controlledErasure d) = cqOne (controlledErasure d) none := by sorry

end QAlgorithms.Papers.Independent.Support50.P02

end
