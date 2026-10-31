-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P01_eb_no_fixed_matrix_algebra
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P01.eb_no_fixed_matrix_algebra
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T23:14:21.737188+00:00
-- url     : https://prove2.me/theorems/046c688d-637b-4aed-ad2b-df2de355b1ad
-- title:
--   Entanglement breaking excludes a fixed matrix algebra
-- statement:
--   Let $d\ge1$ and let $T:M_d(\mathbb C)\to M_d(\mathbb C)$ be an entanglement-breaking quantum channel. There is no subspace $V\subseteq\mathbb C^d$ of complex Hilbert-space dimension at least two such that
--   $$T(A)=A\quad\text{for every }A\in\operatorname{End}(V).$$
--   Operators on $V$ are embedded by zero on $V^\perp$. The assertion concerns pointwise fixation, rather than setwise invariance.
--
--   This prevents nontrivial noiseless matrix factors in the entanglement-breaking fixed space.
-- source:
--   Quantum channels with polytopic images and image additivity, arXiv:1408.2340v1, PDF p. 8, Lemma 5.1

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

/-- Lemma 5.1, PDF pp.8–9: no matrix algebra End(V) with Hilbert dimension at least two
is fixed pointwise. Setwise invariance would be a different, false assertion. -/
theorem eb_no_fixed_matrix_algebra {d : ℕ} (hd : 0 < d)
    (T : Superop (Fin d) (Fin d)) (hT : IsChannel T) (hEB : IsEB T) :
    ¬ ∃ V : Submodule ℂ (EuclideanSpace ℂ (Fin d)), 2 ≤ Module.finrank ℂ V ∧
      ∀ A, IsSupportedOn V A → T A = A := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P01

end
