-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P07_quantum_stein_threshold
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P07.quantum_stein_threshold
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T04:33:13.658406+00:00
-- url     : https://prove2.me/theorems/bec88602-6cb6-48e2-83fc-ec5fcd1239ac
-- title:
--   7.2
-- statement:
--   All quantum systems below are finite-dimensional complex Hilbert spaces of positive dimension, and logarithms are binary. A normalized state is positive semidefinite with trace one; a subnormalized state has trace at most one. Marginals are partial traces. Tildes denote sandwiched Rényi quantities and bars denote Petz quantities. Their trace functionals are $\widetilde Q_\alpha=\operatorname{Tr}(\sigma^{(1-\alpha)/(2\alpha)}\rho\sigma^{(1-\alpha)/(2\alpha)})^\alpha$ and $\overline Q_\alpha=\operatorname{Tr}(\rho^\alpha\sigma^{1-\alpha})$; the divergences include division by $\operatorname{Tr}\rho$ inside the logarithm. Matrix powers vanish on the kernel, including power zero. The notation $\rho\ll\sigma$ means support inclusion. The upward conditional entropy optimizes the negative divergence over normalized reference states on the conditioning system; the downward entropy uses the actual marginal. The notation $H(A|B)=H(AB)-H(B)$ denotes conditional von Neumann entropy. In hypothesis testing, $\alpha_n(T;\rho)=\operatorname{Tr}((I-T)\rho^{\otimes n})$ and $\beta_n(T;\sigma)=\operatorname{Tr}(T\sigma^{\otimes n})$, with $0\le T\le I$. The value $\alpha_n^*(u)$ minimizes the first error subject to the second being at most $u$.
--
--   For normalized ρ≪σ, α_n^*(exp(−nR);ρ,σ) tends to 0 if R<D(ρ||σ), and to 1 if R>D(ρ||σ); no assertion at equality. Define α^* consistently with the preceding prose and (7.1)–(7.2), correcting swapped labels in (7.6).
--
--   $$
--   \lim_{n\to\infty}\alpha_n^*(2^{-nR};\rho,\sigma)=\begin{cases}0,&R<D(\rho\|\sigma),\\1,&R>D(\rho\|\sigma).\end{cases}
--   $$
--
--   This result records the source’s operational or structural relation, with the stated endpoint and attainment clauses retained.
-- source:
--   Quantum Information Processing with Finite Resources -- Mathematical Foundations, arXiv:1504.00233v5, PDF p. 115, 7.2

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

/-- NODE paper:1504.00233#7.2
Theorem 7.2, PDF p.115, using the corrected convention in (7.6) on p.114.
Printed: alpha(T;sigma), beta(T;rho). Changed: alpha(T;rho), beta(T;sigma).
Why: (7.1)-(7.2) and the preceding testing problem fix these hypothesis roles. -/
theorem quantum_stein_threshold [Nonempty I] (r s : paperMat I) (hr : IsDensityMatrix r) (hs : IsDensityMatrix s)
    (hc : paperSupported r s) (R : ℝ) :
    ((R:EReal) < paperRelativeD r s → Tendsto (fun n : ℕ => alphaStar (paperTensorPower r n) (paperTensorPower s n) ((2:ℝ)^(-(n:ℝ)*R))) atTop (nhds 0)) ∧
    (paperRelativeD r s < (R:EReal) → Tendsto (fun n : ℕ => alphaStar (paperTensorPower r n) (paperTensorPower s n) ((2:ℝ)^(-(n:ℝ)*R))) atTop (nhds 1)) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P07

end
