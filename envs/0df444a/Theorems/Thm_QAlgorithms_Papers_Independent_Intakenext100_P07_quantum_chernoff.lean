-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P07_quantum_chernoff
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P07.quantum_chernoff
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T04:32:36.334291+00:00
-- url     : https://prove2.me/theorems/4584a156-59c6-408c-83e2-b4300d8436b8
-- title:
--   7.1
-- statement:
--   All quantum systems below are finite-dimensional complex Hilbert spaces of positive dimension, and logarithms are binary. A normalized state is positive semidefinite with trace one; a subnormalized state has trace at most one. Marginals are partial traces. Tildes denote sandwiched Rényi quantities and bars denote Petz quantities. Their trace functionals are $\widetilde Q_\alpha=\operatorname{Tr}(\sigma^{(1-\alpha)/(2\alpha)}\rho\sigma^{(1-\alpha)/(2\alpha)})^\alpha$ and $\overline Q_\alpha=\operatorname{Tr}(\rho^\alpha\sigma^{1-\alpha})$; the divergences include division by $\operatorname{Tr}\rho$ inside the logarithm. Matrix powers vanish on the kernel, including power zero. The notation $\rho\ll\sigma$ means support inclusion. The upward conditional entropy optimizes the negative divergence over normalized reference states on the conditioning system; the downward entropy uses the actual marginal. The notation $H(A|B)=H(AB)-H(B)$ denotes conditional von Neumann entropy. In hypothesis testing, $\alpha_n(T;\rho)=\operatorname{Tr}((I-T)\rho^{\otimes n})$ and $\beta_n(T;\sigma)=\operatorname{Tr}(T\sigma^{\otimes n})$, with $0\le T\le I$. The value $\alpha_n^*(u)$ minimizes the first error subject to the second being at most $u$.
--
--   For any two normalized states, lim_n −(1/n)log min_{0≤T≤I}(α_n(T;ρ)+β_n(T;σ))/2 = max_{0≤s≤1} −log Tr ρ^s σ^(1−s), with endpoint support projections and extended infinity when orthogonal.
--
--   $$
--   \lim_{n\to\infty}-\frac1n\log_2\min_{0\le T_n\le I}\frac{\alpha_n(T_n;\rho)+\beta_n(T_n;\sigma)}2=\max_{0\le s\le1}-\log_2\operatorname{Tr}(\rho^s\sigma^{1-s}).
--   $$
--
--   This result records the source’s operational or structural relation, with the stated endpoint and attainment clauses retained.
-- source:
--   Quantum Information Processing with Finite Resources -- Mathematical Foundations, arXiv:1504.00233v5, PDF p. 114, 7.1

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P07

noncomputable section

open Filter

open scoped BigOperators Matrix ComplexConjugate ComplexOrder Matrix.Norms.L2Operator Topology

namespace QAlgorithms.Papers.Independent.Intakenext100.P07

attribute [local instance] Classical.propDecidable Classical.decEq

variable {I J A B C D X Y Z : Type*}

variable [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

variable [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

variable [Fintype C] [DecidableEq C] [Fintype D] [DecidableEq D]

variable [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]

variable [Fintype Z] [DecidableEq Z]

/-- NODE paper:1504.00233#7.1
7.1, arXiv:1504.00233v5, PDF p.114. -/
theorem quantum_chernoff [Nonempty I] (r s : paperMat I) (hr : IsDensityMatrix r) (hs : IsDensityMatrix s) :
    ∃ a ∈ Set.Icc (0:ℝ) 1,
      (∀ b ∈ Set.Icc (0:ℝ) 1, -paperLogE (paperRenyiQ false r s b) ≤ -paperLogE (paperRenyiQ false r s a)) ∧
      Tendsto (fun n : ℕ => ((1/(n:ℝ):ℝ):EReal)*(-paperLogE (paperSymmetricError (paperTensorPower r n) (paperTensorPower s n))))
        atTop (nhds (-paperLogE (paperRenyiQ false r s a))) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P07

end
