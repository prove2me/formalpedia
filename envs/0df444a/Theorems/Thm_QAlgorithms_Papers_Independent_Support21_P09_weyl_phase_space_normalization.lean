-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P09_weyl_phase_space_normalization
-- name    : QAlgorithms.Papers.Independent.Support21.P09.weyl_phase_space_normalization
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T03:49:12.898779+00:00
-- url     : https://prove2.me/theorems/b92fbcc6-6d81-4a49-aff0-f19c7913047c
-- title:
--   Finite Weyl phase-space POVM normalization
-- statement:
--   Let $k\ge2$, $m=2^k$, $\omega=e^{2\pi i/m}$, and let $\psi\in\mathbb C^m$ be a unit vector. Write $S|r\rangle=|r+1\bmod m\rangle$ and $T|r\rangle=\omega^r|r\rangle$. The $m^2$ labeled effects
--
--   $$
--   E_{j,l}=\frac1m S^jT^l|\psi\rangle\langle\psi|(T^l)^\dagger(S^j)^\dagger,\qquad 0\le j,l<m,
--   $$
--
--   are positive, nonzero rank-one operators and satisfy
--
--   $$
--   \sum_{j,l}E_{j,l}=I_m.
--   $$
--
--   Conjugation by either $S$ or $T$ preserves the labeled family. This gives the finite phase-space POVM for every physical unit seed; effects that coincide retain their separate labels. No quantitative localization claim or continuous integral is part of this normalization statement.
-- source:
--   Implementation of group-covariant POVMs by orthogonal measurements, arXiv:quant-ph/0407054v1, PDF p. 18, §6.3: finite phase-space POVM normalization

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P09

noncomputable section

namespace QAlgorithms.Papers.Independent.Support21.P09

open scoped BigOperators ComplexConjugate

open QAlgorithms.Papers.Independent.Frontier18.P17 (clock)

/-- PDF pp.16–18, §6.3: normalized physical Weyl phase-space POVM. Localization is
interpretive motivation and is not needed for this finite normalization identity. -/
theorem weyl_phase_space_normalization (k : ℕ) (hk : 2 ≤ k)
    (psi : EuclideanSpace ℂ (Fin (2 ^ k))) (hpsi : ‖psi‖ = 1) :
    IsPOVM (phaseSpaceEffect (2 ^ k) psi) ∧
    (∀ p, phaseSpaceEffect (2 ^ k) psi p ≠ 0) ∧
    (∀ U ∈ ({positiveShift (2 ^ k), clock (2 ^ k)} : Set _), ∀ p,
      ∃ q, U * phaseSpaceEffect (2 ^ k) psi p * U.conjTranspose =
        phaseSpaceEffect (2 ^ k) psi q) := by sorry

end QAlgorithms.Papers.Independent.Support21.P09

end
