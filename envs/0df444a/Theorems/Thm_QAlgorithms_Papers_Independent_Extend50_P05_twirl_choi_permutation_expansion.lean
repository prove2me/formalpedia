-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P05_twirl_choi_permutation_expansion
-- name    : QAlgorithms.Papers.Independent.Extend50.P05.twirl_choi_permutation_expansion
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T13:20:07.114062+00:00
-- url     : https://prove2.me/theorems/349a2387-8065-48a4-b733-9bceaea34985
-- title:
--   Permutation expansion of a twirled channel
-- statement:
--   Let $d,N\ge1$ and let $T:M_d\to M_d^{\otimes N}$ be any complex-linear CPTP map. Its symmetrization is the normalized-Haar integral $\widetilde T(X)=\int U^{\otimes N}T(U^*XU)(U^*)^{\otimes N}\,dU$. In the fixed computational basis, let $C_{\widetilde T}=\sum_{a,b}|a\rangle\langle b|\otimes\widetilde T(|a\rangle\langle b|)$ be the unnormalized, input-first Choi matrix. Then
--
--   $$
--   C_{\widetilde T}=\sum_{\pi\in S_{N+1}}\alpha_\pi V(\pi)^\Gamma
--   \qquad\text{for some }\alpha_\pi\in\mathbb C.
--   $$
--
--   Here $V(\pi)$ permutes tensor factors by the inverse permutation and $\Gamma$ transposes only the input factor. No uniqueness or independence of the coefficients is asserted.
--
--   The expansion reduces symmetrized cloning to physical permutation operators.
-- source:
--   A geometrical description of the universal $1 \to 2$ asymmetric quantum cloning region, arXiv:2106.09655v1, PDF p. 5, Lemma 1: expansion in partially transposed physical permutations

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P05

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.Elementwise

open MeasureTheory

namespace QAlgorithms.Papers.Independent.Extend50.P05

open QAlgorithms.Papers.Independent.Information100.P34 (choi)

open QAlgorithms.Papers.Independent.Information100.P60 (isotropic)

open QAlgorithms.Papers.Independent.Information100.P63 (tensorPower)

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

/-- PDF p.5, Lemma 1 (twirl defined on p.4): existence, without coefficient uniqueness. -/
theorem twirl_choi_permutation_expansion (d N : ℕ) (hd : 1 ≤ d) (hN : 1 ≤ N)
    (T : Superop (Fin d) (CloningOutputs d N)) (hT : IsChannel T) :
    ∃ alpha : Equiv.Perm (Fin (N + 1)) → ℂ,
      choi (cloningTwirl T) = ∑ pi, alpha pi •
        Entanglement.partialTransposeFirst (physicalPermutation d N pi) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P05

end
