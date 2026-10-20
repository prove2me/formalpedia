-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P31_spectrumDependsOnLastBox
-- name    : QAlgorithms.Papers.Independent.Dependency50.P31.spectrumDependsOnLastBox
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T14:38:39.143132+00:00
-- url     : https://prove2.me/theorems/ba39c6fd-330e-4d25-8fac-d83dca1506d2
-- title:
--   The full Schmidt spectrum depends only on the last box
-- statement:
--   Let $\nu$ have $N\ge2$ boxes and let $d\ge c_1$. Realize the multiplicity factor as $V^\nu=\operatorname{Hom}_{S_N}(S^\nu,(\mathbb C^d)^{\otimes N})$, where $S^\nu$ is the concrete Specht representation. Choose unit Young orthogonal vectors $|t\rangle$ in its Hermitian projector lines, independently of $v\in V^\nu$, and put $\psi_t=v(|t\rangle)$. If standard tableaux $t,s$ of shape $\nu$ have their label $N$ in the same box, then their complete Schmidt spectra at the final-particle cut agree:
--
--   $$
--   \bigl(\lambda_i(\psi_t)\bigr)_{i=1}^d
--   =\bigl(\lambda_i(\psi_s)\bigr)_{i=1}^d.
--   $$
--
--   The same $v$ is used on both sides. The statement is homogeneous, so normalization is unnecessary and $v=0$ is included.
--
--   **Formalization Note** Lean states equality of the characteristic polynomials of the two positive last marginals. This is equivalent to equality of their eigenvalues with multiplicities, hence of all nonnegative Schmidt amplitudes, including zeros. Choices of phases of $|t\rangle$ have no effect.
-- source:
--   Lower bound on entanglement in subspaces defined by Young diagrams, arXiv:1805.00364v2, PDF p. 15, Lemma 11, equations (50)–(51)

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P31

noncomputable section

namespace QAlgorithms.Papers.Independent.Dependency50.P31

open scoped ComplexConjugate

open QAlgorithms.Papers.Independent.Information100.P58 (Word)

attribute [local instance] Classical.propDecidable

/-- Lemma 11, arXiv:1805.00364v2 PDF p.15, equations (50)-(51).
For one common multiplicity vector, all squared Schmidt coefficients agree, including
multiplicities and zeros. Equality of characteristic polynomials of the positive
last marginals is equivalent to equality of the whole Schmidt spectrum. The statement
is homogeneous in v and therefore also covers the source's unnormalized vectors. -/
theorem spectrumDependsOnLastBox {d n : ℕ} (hn : 2 ≤ n) (nu : Schur.Partition d n)
    (v : MultiplicitySpace nu) (t s : Filling n)
    (ht : IsTableau nu.val t) (hs : IsTableau nu.val s)
    (hbox : lastBox t (by omega) = lastBox s (by omega)) :
    (lastMarginal (tableauState v t)).charpoly =
      (lastMarginal (tableauState v s)).charpoly := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P31

end
