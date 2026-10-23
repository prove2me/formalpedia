-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier18_P14_canonicalConstraints
-- name    : QAlgorithms.Papers.Independent.Frontier18.P14.canonicalConstraints
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T09:02:36.624984+00:00
-- url     : https://prove2.me/theorems/4615db61-5828-46c0-8971-6c57ce46fcff
-- title:
--   Canonical constraints and passive photon-number conservation
-- statement:
--   Let there be $n$ input and $n$ output bosonic modes, with all vacuum ports retained. On their finite-occupation invariant core, let $a'_j=\sum_k(B_{jk}a_k+C_{jk}a_k^\dagger)$ and let $a_j'{}^\dagger$ be their actual conjugate partners. Assume the output operators obey the Bose commutation relations. For the doubled matrix $S=\begin{pmatrix}B&C\\\overline C&\overline B\end{pmatrix}$ and $G=\operatorname{diag}(I,-I)$,
--
--   $$SGS^\dagger=G,\qquad S^{-1}=GS^\dagger G,\qquad |\det S|^2=1.$$
--
--   If $C=0$, then $\sum_j a_j'{}^\dagger a'_j=\sum_j a_j^\dagger a_j$. These identities describe canonical reversible networks; the last is photon-number conservation. No assertion of energy conservation for mixing unequal frequencies is made.
-- source:
--   Quantum Physics of Simple Optical Instruments, arXiv:quant-ph/0305007v2, PDF p. 9, §3.1: canonical matrix constraints and photon-number conservation

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P14

noncomputable section

open scoped Matrix ComplexConjugate

open Filter

attribute [local instance] Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Frontier18.P14

open QAlgorithms.Papers.Independent.Dependency50.P34 (fockKet)

/-- PDF pp.9–10, (3.4)–(3.7): square finite reversible networks, with all
vacuum ports retained. Proper output CCR imply quasi-unitarity, the displayed
inverse, determinant modulus one, and passive total-number conservation.
No energy conservation across unequal-frequency mixing is asserted. -/
theorem canonicalConstraints
    (n : ℕ) (B C : Matrix (Fin n) (Fin n) ℂ)
    (hcanon : ∀ i j,
      commutator (outputAnnihilator B C i) (outputCreator B C j) =
        if i = j then 1 else 0)
    (hcomm : ∀ i j,
      commutator (outputAnnihilator B C i) (outputAnnihilator B C j) = 0) :
    doubled B C * modeMetric n * (doubled B C).conjTranspose = modeMetric n ∧
    (doubled B C)⁻¹ = modeMetric n * (doubled B C).conjTranspose * modeMetric n ∧
    Complex.normSq (Matrix.det (doubled B C)) = 1 ∧
    (C = 0 → ∑ j, outputCreator B C j * outputAnnihilator B C j =
      ∑ j, create n j * annihilate n j) := by sorry

end QAlgorithms.Papers.Independent.Frontier18.P14

end
