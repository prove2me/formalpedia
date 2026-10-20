-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P11_unital_entropy_nondecreasing
-- name    : QAlgorithms.Papers.Independent.Dependency50.P11.unital_entropy_nondecreasing
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T13:36:04.503303+00:00
-- url     : https://prove2.me/theorems/58566b9a-bb9a-49b2-801c-2de217360344
-- title:
--   Unital channels do not decrease entropy
-- statement:
--   Let $d\ge1$, let $\mathcal E$ be a completely positive, trace-preserving linear map on operators on $\mathbb C^d$ with $\mathcal E(I_d)=I_d$, and let $\rho$ be any positive trace-one density matrix. Write $S(\rho)=-\operatorname{Tr}(\rho\log\rho)$, using natural logarithms and the convention $0\log0=0$. Then
--
--   $$S(\mathcal E(\rho))\ge S(\rho).$$
--
--   The inequality includes singular states and describes the entropy monotonicity of a unital channel. No repeated implementation is needed for this one-use result.
-- source:
--   Repeatable quantum memory channels, arXiv:0808.3851v1, PDF p. 5, Appendix A, Lemma 1

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P11

noncomputable section

namespace QAlgorithms.Papers.Independent.Dependency50.P11

open scoped Matrix ComplexConjugate ComplexOrder

open QAlgorithms.Papers.Independent.Information100.P23 (Operator)

/-- Appendix A, Lemma 1, PDF p.5: unital CPTP maps do not decrease von Neumann entropy.
Singular density inputs are included, with zero eigenvalues contributing zero. -/
theorem unital_entropy_nondecreasing {d : ℕ} (hd : 0 < d)
    (E : Superop (Fin d) (Fin d)) (hE : IsChannel E) (hU : IsUnital E)
    (rho : Operator d) (hrho : IsDensityMatrix rho) :
    vonNeumannEntropy rho ≤ vonNeumannEntropy (E rho) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P11

end
