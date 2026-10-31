-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P01_polytopic_entropy_nonadditivity
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P01.polytopic_entropy_nonadditivity
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T23:13:30.836596+00:00
-- url     : https://prove2.me/theorems/07ff93d3-8cb1-46f8-a0ef-cbdd46100752
-- title:
--   Polytopic images can violate entropy additivity
-- statement:
--   For every real $p\ge1$, there exist positive integers $d,n$ and a quantum channel $T:M_d(\mathbb C)\to M_n(\mathbb C)$ with polytopic state image such that
--   $$H_{\min}^{(p)}(T\otimes\overline T)<2H_{\min}^{(p)}(T),\qquad H_{\min}^{(p)}(\overline T)=H_{\min}^{(p)}(T).$$
--   Here $\overline T(A)=\overline{T(\overline A)}$, and $H_{\min}^{(p)}$ is the minimum of the output Rényi entropy over input density matrices. For $p>1$, $H^{(p)}(\rho)=\log_2\operatorname{Tr}(\rho^p)/(1-p)$; for $p=1$, $H^{(1)}(\rho)=-\operatorname{Tr}(\rho\log_2\rho)$, with $0\log 0=0$. The dimensions and channel may depend on $p$.
--
--   This establishes strict nonadditivity within the polytopic-image class. **Formalization Note** The printed missing minus sign at $p=1$ is corrected to agree with the stated limit; the correction awaits independent moderation.
-- source:
--   Quantum channels with polytopic images and image additivity, arXiv:1408.2340v1, PDF p. 7, Theorem 4.1

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P01

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open Filter

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

namespace QAlgorithms.Papers.Independent.Intakenext100.P01

open QAlgorithms.Papers.Independent.Information100.P44 (Mat)

open QAlgorithms.Papers.Independent.Information100.P07 (projection)

open QAlgorithms.Papers.Independent.Dependency50.P23 (IsEB)

open QAlgorithms.Papers.Independent.Dependency50.P05 (renyiEntropy)

/-- Theorem 4.1, PDF pp.7–8: strict subadditivity for each real p≥1. Dimensions and
channel may depend on p. Source correction: p.7 prints +sum x log x at p=1;
changed to -sum x log_2 x because the source defines this value by the p-to-1 limit.
The unspecified logarithm base is fixed to two, a common positive rescaling. -/
theorem polytopic_entropy_nonadditivity (p : ℝ) (hp : 1 ≤ p) :
    ∃ d n : ℕ, 0 < d ∧ 0 < n ∧ ∃ T : Superop (Fin d) (Fin n),
      IsChannel T ∧ IsPolytopic (channelImage T) ∧
      minimumOutputRenyiEntropy p (conjugateMap T) = minimumOutputRenyiEntropy p T ∧
      minimumOutputRenyiEntropy p (tensorOnFunctions T (conjugateMap T)) <
        2 * minimumOutputRenyiEntropy p T := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P01

end
