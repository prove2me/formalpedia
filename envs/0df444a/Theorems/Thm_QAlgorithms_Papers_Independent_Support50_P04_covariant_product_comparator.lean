-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P04_covariant_product_comparator
-- name    : QAlgorithms.Papers.Independent.Support50.P04.covariant_product_comparator
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T18:36:38.900285+00:00
-- url     : https://prove2.me/theorems/06f99a6e-63e1-47ec-b212-f8adff140d69
-- title:
--   Covariant product-alternative testing converse
-- statement:
--   Let $\mathcal N:A\to B$ be a CPTP channel on finite positive-dimensional complex Hilbert spaces with fixed orthonormal bases. Write $\widehat R(n;\varepsilon)$ and $\widehat R^{\mathrm{cpp}}(n;\varepsilon)$ for the maximum unassisted and classical-post-processing assisted entanglement-transmission rates. A code has a positive integer message dimension $M$, rate $\log_2 M/n$, and squared fidelity to the normalized maximally entangled target at least $1-\varepsilon$. A cpp encoder may retain sender memory; its decoder is LOCC across that memory and the receiver outputs, with its final quantum output at the receiver and no preshared entanglement. Let $n\ge1$ and $0<\varepsilon<1$, and assume covariance with respect to the full input unitary group, with an output unitary representation. Set $\omega=(\mathrm{id}\otimes\mathcal N)(\Phi_A)$ and use the normalized target. Then
--
--   $$\widehat R^{\mathrm{cpp}}(n;\varepsilon)\le\inf_{\sigma\in\mathrm{PPT}^{\prime}(A:B)}\frac1n D_H^\varepsilon(\omega^{\otimes n}\|\sigma^{\otimes n}).$$
--
--   The product restriction concerns the comparator only; codes may encode arbitrary entangled inputs.
-- source:
--   Quantum Coding with Finite Resources, arXiv:1504.04617v2, PDF p. 12, Eq. (39)

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P04

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open QAlgorithms

namespace QAlgorithms.Papers.Independent.Support50.P04

variable {A B E : Type} [Fintype A] [DecidableEq A]

variable [Fintype B] [DecidableEq B] [Fintype E] [DecidableEq E]

/-- arXiv:1504.04617v2, PDF pp.12–13, Eq.(39): product ALTERNATIVES relax the
converse; actual code inputs remain arbitrary, including entangled blocked inputs. -/
theorem covariant_product_comparator [Nonempty A] [Nonempty B]
    (N : Superop A B) (hN : IsChannel N) (hcov : FullUnitaryCovariant N)
    (n : ℕ) (hn : 0 < n) (epsilon : ℝ) (he0 : 0 < epsilon) (he1 : epsilon < 1) :
    cppBoundary N n epsilon ≤ sInf {v | ∃ sigma : Matrix (A × B) (A × B) ℂ,
      QAlgorithms.Papers.Independent.Dependency50.P36.pptPrime sigma ∧
      v = QAlgorithms.Papers.Independent.Dependency50.P36.testingEntropy (QAlgorithms.Papers.Independent.Information100.P60.copies n (choiState N)) (QAlgorithms.Papers.Independent.Information100.P60.copies n sigma) epsilon / (n : EReal)} := by sorry

end QAlgorithms.Papers.Independent.Support50.P04

end
