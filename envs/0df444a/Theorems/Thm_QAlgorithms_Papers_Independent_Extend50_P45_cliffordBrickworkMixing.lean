-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P45_cliffordBrickworkMixing
-- name    : QAlgorithms.Papers.Independent.Extend50.P45.cliffordBrickworkMixing
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T21:07:35.194726+00:00
-- url     : https://prove2.me/theorems/1e6ce074-0eee-41a2-bdf4-d6150f9d08d3
-- title:
--   Uniform mixing toward global Clifford moments
-- statement:
--   Let $n\ge2$ be even and let $t\ge1$ be an integer. Let $\nu_n^{{\rm Cl},{\rm bw}}$ be one periodic two-matching brickwork step with every two-qubit gate independently uniform on the full two-qubit Clifford group modulo phase. Let $\mu_{\rm Cl}$ be uniform on the full global $n$-qubit Clifford group modulo phase. For $M(\nu,t)=\mathbb E[U^{\otimes t}\otimes\overline U^{\otimes t}]$,
--   $$\left\|M(\nu_n^{{\rm Cl},{\rm bw}},t)-M(\mu_{\rm Cl},t)\right\|_\infty\le1-\frac1{2000n^3}.$$
--   This uniform-in-$t$ estimate compares Clifford moments; its target is the global Clifford law. Finite-type instances in Lean enumerate the entire frozen projective groups, with no spectral assumptions.
-- source:
--   Random quantum circuits are approximate unitary $t$-designs in depth $O\left(nt^{5+o(1)}\right)$, arXiv:2203.16571v3, PDF p. 13, Lemma 6: uniform global-Clifford mixing from Clifford brickwork, Eq.(50)

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P45

noncomputable section

open MeasureTheory

open scoped ComplexConjugate ENNReal

namespace QAlgorithms.Papers.Independent.Extend50.P45

attribute [local instance] QAlgorithms.Papers.Independent.Extend50.P45.qubitMatrixMeasurable

attribute [local instance] QAlgorithms.Papers.Independent.Extend50.P45.qubitMatrixBorel

/-- PDF p.13, Lemma 6, Eq.(50): uniform over all positive moments, and mixing
TOWARD GLOBAL CLIFFORD moments, not Haar moments. One step is two layers. -/
theorem cliffordBrickworkMixing (n t : ℕ)
    [Fintype (Clifford.ProjectiveGroup n)] [Fintype (Clifford.ProjectiveGroup 2)]
    (hn : 2 ≤ n) (heven : Even n) (ht : 1 ≤ t) :
    specNorm (balancedUnitaryMoment (cliffordBrickworkLaw n) t -
      balancedUnitaryMoment (cliffordLaw n) t) ≤
      1 - ((2000 : ℝ) * (n : ℝ) ^ 3)⁻¹ := by sorry

end QAlgorithms.Papers.Independent.Extend50.P45

end
