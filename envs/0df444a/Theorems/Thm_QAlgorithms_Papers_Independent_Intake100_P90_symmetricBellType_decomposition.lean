-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P90_symmetricBellType_decomposition
-- name    : QAlgorithms.Papers.Independent.Intake100.P90.symmetricBellType_decomposition
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T11:09:59.992487+00:00
-- url     : https://prove2.me/theorems/b0ba26cc-ddd7-4502-8f04-bd3d0354c38f
-- title:
--   Symmetric Bell-type decomposition after bilateral randomization
-- statement:
--   Let $\rho$ be any normalized state of $n$ Alice--Bob qubit pairs, including a state produced by a coherent attack. Independently on each pair, apply the uniform bilateral Pauli randomization $\mathcal D_2$, and then average over all simultaneous pair permutations $\mathcal P_S$. Use the Bell order $\Phi_1=(00+11)/\sqrt2$, $\Phi_2=(00-11)/\sqrt2$, $\Phi_3=(10+01)/\sqrt2$, $\Phi_4=(10-01)/\sqrt2$, with kets understood. For each type $t=(n_1,n_2,n_3,n_4)$ of nonnegative integers summing to $n$, define $\lambda_t$ by summing the actual Bell-product measurement probabilities of $\rho$ over all words of that type. These constructed coefficients are nonnegative and sum to one, and
--
--   $$\mathcal P_S(\mathcal D_2^{\otimes n}(\rho))=\sum_{n_1+\cdots+n_4=n}\lambda_t\,\mathcal P_S(P_{\Phi_1}^{\otimes n_1}\otimes P_{\Phi_2}^{\otimes n_2}\otimes P_{\Phi_3}^{\otimes n_3}\otimes P_{\Phi_4}^{\otimes n_4}).$$
--
--   The output is a normalized density matrix and a convex mixture of tensor products of normalized pair states. This is separability across distinct $AB$ pair blocks, not between Alice and Bob. It imposes no condition on subsequent classical postprocessing and therefore applies also when that processing is two-way.
--
--   **Formalization Note** Both randomizations are uniform averages. The source's displayed $\mathcal D_2$ omits its $1/4$ normalization. Occupation numbers are bounded naturals with an exact sum constraint, without truncated subtraction.
-- source:
--   Lower and upper bounds on the secret key rate for QKD protocols using one--way classical communication, arXiv:quant-ph/0410215v2, PDF p. 2, Eq. (1): symmetric mixture of Bell-type product projectors

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P90

noncomputable section

open scoped ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Intake100.P90

/-- PDF p.2, Eq.(1), with the normalized D2 and P_S averages. Any normalized
n-pair state yields the displayed type mixture and is separable across pair
blocks after independent bilateral twirling and common permutation. The input
can arise from arbitrary coherent attacks and arbitrary protocol filters;
no restriction on later (one-way or two-way) CPP is made. -/
theorem symmetricBellType_decomposition (n : ℕ)
    (rho : Matrix (Fin n → (Bool × Bool)) (Fin n → (Bool × Bool)) ℂ)
    (hrho : IsDensityMatrix rho) :
    (∀ t : BellType n, 0 ≤ bellTypeWeight rho t) ∧
    (∑ t : BellType n, bellTypeWeight rho t) = 1 ∧
    pairSymmetrize (independentPairTwirl rho) =
      ∑ t : BellType n, (bellTypeWeight rho t : ℂ) •
        pairSymmetrize (pureDensity (bellWord (sortedBellWord t))) ∧
    IsDensityMatrix (pairSymmetrize (independentPairTwirl rho)) ∧
    IsPairBlockSeparable (pairSymmetrize (independentPairTwirl rho)) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P90

end
