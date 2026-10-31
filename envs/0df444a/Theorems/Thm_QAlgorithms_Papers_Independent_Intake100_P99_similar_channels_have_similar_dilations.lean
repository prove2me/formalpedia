-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P99_similar_channels_have_similar_dilations
-- name    : QAlgorithms.Papers.Independent.Intake100.P99.similar_channels_have_similar_dilations
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T16:15:17.526267+00:00
-- url     : https://prove2.me/theorems/95936a46-4dcb-45ea-b4f6-00b663710f9f
-- title:
--   Similar finite-dimensional channels have similar dilations
-- statement:
--   Let $\mathcal E_0,\mathcal E_1$ be completely positive trace-preserving channels from a system of positive dimension $d$ to a system of positive dimension $d'$. If $\|\mathcal E_0-\mathcal E_1\|_\diamond<\varepsilon$, there exist isometric dilations $U_0,U_1:S\to T\otimes E$ with a common environment of dimension $dd'$ such that
--
--   $$
--   \mathcal E_j(X)=\operatorname{Tr}_E(U_j XU_j^\dagger)\quad(j=0,1),\qquad
--   \|U_0-U_1\|_{\mathrm{sup}}^2<d\varepsilon.
--   $$
--
--   The channel identities hold for every input operator $X$. The diamond norm is the full stabilized trace norm, using a reference of dimension $d$, and $\|\cdot\|_{\mathrm{sup}}$ is the Hilbert-space operator norm. This gives a common-environment comparison of actual channel realizations.
--
--   **Formalization Note** The appendix uses an unnormalized Choi vector with squared norm $d$; no normalized-state assumption is placed on that auxiliary operator here.
-- source:
--   Security of quantum key distribution with imperfect devices, arXiv:quant-ph/0212066v3, PDF p. 14, Lemma 4: similar channels have similar dilations

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P99

noncomputable section

open scoped Matrix ComplexConjugate BigOperators

namespace QAlgorithms.Papers.Independent.Intake100.P99

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms

open QAlgorithms.Papers.Independent.Information100.P69 (diamond)

open QAlgorithms.Papers.Independent.Dependency50.P48 (IsDilation receiver)

/-- arXiv:quant-ph/0212066v3, PDF p.14, Lemma 4; Appendix A, pp.20--21.
The full rectangular diamond norm is stabilized with a reference of dimension d.
The common environment has dimension d*t; the strict squared L2 operator-norm
bound has factor d, not d squared. Both system dimensions are nonzero. -/
theorem similar_channels_have_similar_dilations
    (d t : ℕ) (hd : 0 < d) (ht : 0 < t)
    (E0 E1 : Superop (Fin d) (Fin t))
    (hE0 : IsChannel E0) (hE1 : IsChannel E1)
    (epsilon : ℝ) (hclose : diamond (E0 - E1) < epsilon) :
    ∃ U0 U1 : Matrix (Fin t × Fin (d * t)) (Fin d) ℂ,
      IsDilation U0 ∧ receiver U0 = E0 ∧
      IsDilation U1 ∧ receiver U1 = E1 ∧
      specNorm (U0 - U1) ^ 2 < (d : ℝ) * epsilon := by sorry

end QAlgorithms.Papers.Independent.Intake100.P99

end
