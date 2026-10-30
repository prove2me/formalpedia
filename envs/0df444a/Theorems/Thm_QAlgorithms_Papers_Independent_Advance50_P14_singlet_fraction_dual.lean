-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P14_singlet_fraction_dual
-- name    : QAlgorithms.Papers.Independent.Advance50.P14.singlet_fraction_dual
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T10:16:44.224983+00:00
-- url     : https://prove2.me/theorems/18092a52-b328-47ae-a31a-074573bc7b98
-- title:
--   Lemma IV.3, equations (12)–(13): singlet-fraction dual
-- statement:
--   All systems are finite-dimensional complex multipartite systems with at least two parties and positive local dimensions. Every state is positive semidefinite with trace one. Separability means a convex mixture of products across all parties. Logarithms are base two, and the trace norm has no factor of one half. An operation is CPTP; its separability constraint applies only to the specified input and output partitions. Let $K\ge1$ be an integer, and let $\Phi_K=K^{-1}\sum_{i,j=1}^K|ii\rangle\langle jj|$ on the first two output parties; all others are trivial. For any state $\rho$,
--
--   $$\max_{\Lambda\in{\rm SEPP}}\operatorname{Tr}(\Phi_K\Lambda(\rho))=\min_{Z\in\operatorname{cone}(\mathcal S)}\left[\operatorname{Tr}(\rho-Z)_++\frac{\operatorname{Tr}Z}{K}\right].$$
--
--   Both extrema are attained. Here $\mathcal S$ is the input separable-state set, its cone includes zero and unnormalized operators, and $\operatorname{Tr}(A)_+$ is the sum of the positive eigenvalues of a Hermitian operator. This dual description includes $K=1$.
-- source:
--   A reversible theory of entanglement and its relation to the second law, arXiv:0710.5827v3, PDF p. 11, Lemma IV.3, equations (12)–(13): singlet-fraction dual

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P14

noncomputable section

open Filter

open QAlgorithms.Papers.Independent.Claimed50.P33 (RegisterBasis)

open scoped Matrix ComplexOrder ENNReal NNReal

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Advance50.P14

/-- PDF pp.11–12, Lemma IV.3, Eqs.(12)–(13): equality of an ATTAINED
maximum over SEPP channels and an ATTAINED minimum over the unnormalized
input separable cone, including zero. K=1 is included without division by K²−1. -/
theorem singlet_fraction_dual {m : ℕ} (A : MultipartiteRegister m) (rho : PartyOperator A)
    (hrho : IsDensityMatrix rho) (K : ℕ) (hK : 0 < K) :
    ∃ f : ℝ, IsGreatest (singletFractions .strict A rho K hK 0) f ∧
      IsLeast {v | ∃ Z : PartyOperator A, SeparableCone A Z ∧
        v = singletDualObjective A rho Z (1 / (K : ℝ))} f := by sorry

end QAlgorithms.Papers.Independent.Advance50.P14

end
