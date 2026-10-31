-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P07_strong_converse_exponent
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P07.strong_converse_exponent
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T04:33:45.572935+00:00
-- url     : https://prove2.me/theorems/959413e9-8af2-4de9-b9fc-d59ef4479a1b
-- title:
--   7.5
-- statement:
--   All quantum systems below are finite-dimensional complex Hilbert spaces of positive dimension, and logarithms are binary. A normalized state is positive semidefinite with trace one; a subnormalized state has trace at most one. Marginals are partial traces. Tildes denote sandwiched Rényi quantities and bars denote Petz quantities. Their trace functionals are $\widetilde Q_\alpha=\operatorname{Tr}(\sigma^{(1-\alpha)/(2\alpha)}\rho\sigma^{(1-\alpha)/(2\alpha)})^\alpha$ and $\overline Q_\alpha=\operatorname{Tr}(\rho^\alpha\sigma^{1-\alpha})$; the divergences include division by $\operatorname{Tr}\rho$ inside the logarithm. Matrix powers vanish on the kernel, including power zero. The notation $\rho\ll\sigma$ means support inclusion. The upward conditional entropy optimizes the negative divergence over normalized reference states on the conditioning system; the downward entropy uses the actual marginal. The notation $H(A|B)=H(AB)-H(B)$ denotes conditional von Neumann entropy. In hypothesis testing, $\alpha_n(T;\rho)=\operatorname{Tr}((I-T)\rho^{\otimes n})$ and $\beta_n(T;\sigma)=\operatorname{Tr}(T\sigma^{\otimes n})$, with $0\le T\le I$. The value $\alpha_n^*(u)$ minimizes the first error subject to the second being at most $u$.
--
--   For normalized ρ≪σ,R>D(ρ||σ), lim −(1/n)log(1−α_n^*(exp(−nR)))=sup_{s>1} ((s−1)/s)(R−Dtilde_s(ρ||σ)).
--
--   $$
--   \lim_n-\frac1n\log_2(1-\alpha_n^*(2^{-nR}))=\sup_{s>1}\frac{s-1}{s}(R-\widetilde D_s(\rho\|\sigma)).
--   $$
--
--   This result records the source’s operational or structural relation, with the stated endpoint and attainment clauses retained.
-- source:
--   Quantum Information Processing with Finite Resources -- Mathematical Foundations, arXiv:1504.00233v5, PDF p. 116, 7.5

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

/-- NODE paper:1504.00233#7.5
7.5, arXiv:1504.00233v5, PDF p.116. -/
theorem strong_converse_exponent [Nonempty I] (r s : paperMat I) (hr : IsDensityMatrix r) (hs : IsDensityMatrix s)
    (hc : paperSupported r s) (R : ℝ) (hR : paperRelativeD r s < (R:EReal)) :
    Tendsto (fun n : ℕ => ((1/(n:ℝ):ℝ):EReal)*(-paperLogE (1-alphaStar (paperTensorPower r n) (paperTensorPower s n) ((2:ℝ)^(-(n:ℝ)*R)))))
      atTop (nhds (sSup {d : EReal | ∃ a : ℝ, 1 < a ∧
        d = (((a-1)/a:ℝ):EReal)*((R:EReal)-renyiFinite true r s a)})) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P07

end
