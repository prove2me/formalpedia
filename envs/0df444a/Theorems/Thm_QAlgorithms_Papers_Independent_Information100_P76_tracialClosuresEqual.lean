-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P76_tracialClosuresEqual
-- name    : QAlgorithms.Papers.Independent.Information100.P76.tracialClosuresEqual
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T16:04:28.899722+00:00
-- url     : https://prove2.me/theorems/9fd8269a-e679-4dba-8e7c-ea02731322c5
-- title:
--   Section 8, unnumbered: weighted and single-matrix tracial closures coincide
-- statement:
--   Fix a positive finite system dimension $q$. Let $\mathcal T_{\rm weighted}$ be the channels implemented by finitely many sector-preserving unitary blocks, with initializer $\bigoplus_jp_j\pi_{d_j}$ for positive finite sector dimensions and arbitrary nonnegative weights summing to one. Let $\mathcal T_{\rm single}$ be the channels implemented by one finite matrix bath initialized in its maximally mixed state. Their half-diamond approximation closures agree:
--
--   $$\overline{\mathcal T_{\rm weighted}}=\overline{\mathcal T_{\rm single}}.$$
--
--   Zero weights are permitted and there is at least one sector. Approximation dimensions may be selected along feasible multiples; they are not prescribed as every sufficiently large integer. The equality concerns closures and does not identify the exact finite realization classes or assert exact attainment for irrational weights.
-- source:
--   Bath dimension and initial entropy for closed repeated use of a quantum channel, arXiv:2609.18267v1, PDF p. 15, Section 8, unnumbered

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P76

noncomputable section

namespace QAlgorithms.Papers.Independent.Information100.P76

open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.L2Operator

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

open Filter

/-- PDF p.15, Section 8: equality of approximation closures, without exact finite
attainment or equality of the finite realization classes. -/
theorem tracialClosuresEqual {q : ℕ} (hq : 0 < q)
    (Phi : Superop (Fin q) (Fin q)) (hPhi : IsChannel Phi) :
    inWeightedTracialClosure Phi ↔ inSingleTracialClosure Phi := by sorry

end QAlgorithms.Papers.Independent.Information100.P76

end
