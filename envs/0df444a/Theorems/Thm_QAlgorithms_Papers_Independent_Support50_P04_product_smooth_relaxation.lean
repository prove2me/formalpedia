-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P04_product_smooth_relaxation
-- name    : QAlgorithms.Papers.Independent.Support50.P04.product_smooth_relaxation
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T18:39:43.533526+00:00
-- url     : https://prove2.me/theorems/1e5c1c60-189c-4e3d-9645-599b4a74b857
-- title:
--   Product-input smooth-entropy relaxation
-- statement:
--   Let $\mathcal N:A\to B$ be a CPTP channel on finite positive-dimensional complex Hilbert spaces with fixed orthonormal bases. Write $\widehat R(n;\varepsilon)$ and $\widehat R^{\mathrm{cpp}}(n;\varepsilon)$ for the maximum unassisted and classical-post-processing assisted entanglement-transmission rates. A code has a positive integer message dimension $M$, rate $\log_2 M/n$, and squared fidelity to the normalized maximally entangled target at least $1-\varepsilon$. A cpp encoder may retain sender memory; its decoder is LOCC across that memory and the receiver outputs, with its final quantum output at the receiver and no preshared entanglement. Use one finite-dimensional isometry $U:A\hookrightarrow B\otimes E$ and its receiver/complementary channels. Let $n\ge1$, $0<\varepsilon<1$, and $1/\sqrt n<\varepsilon$. For a normalized center $\omega$, define $H_{\min}^{\delta}(A|E)_\omega$ as the supremum of real $\lambda$ for which there exist $\bar\omega\succeq0$ of trace at most one and a normalized density $\sigma_E$ such that $F(\bar\omega,\omega)\ge1-\delta^2$ and $\bar\omega\preceq2^{-\lambda}I_A\otimes\sigma_E$. Supremums are taken in the extended reals. For each normalized single-use density input $\rho$, put $\omega^\rho=(\mathrm{id}\otimes\mathcal N^c)(\psi^\rho)$ and $\delta_n=\sqrt{\varepsilon-1/\sqrt n}$. Then
--
--   $$\widehat R(n;\varepsilon)\ge\sup_{\rho\in\mathcal S(A)}\frac{H_{\min}^{\delta_n}(A^n|E^n)_{(\omega^\rho)^{\otimes n}}-2\log_2 n-1}{n}.$$
--
--   This is the product-input relaxation of the optimized inner bound.
-- source:
--   Quantum Coding with Finite Resources, arXiv:1504.04617v2, PDF p. 14, Eq. (47)

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P04

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open QAlgorithms

namespace QAlgorithms.Papers.Independent.Support50.P04

variable {A B E : Type} [Fintype A] [DecidableEq A]

variable [Fintype B] [DecidableEq B] [Fintype E] [DecidableEq E]

/-- arXiv:1504.04617v2, PDF p.14, Eq.(47).
Printed delta=sqrt(epsilon)-1/sqrt(n), n>1/epsilon; changed by the paragraph's
eta=1/sqrt(n) substitution in (46) to delta=sqrt(epsilon-1/sqrt(n)), 1/sqrt(n)<epsilon. -/
theorem product_smooth_relaxation [Nonempty A] [Nonempty B] [Nonempty E]
    (U : Matrix (B × E) A ℂ) (hU : Uᴴ * U = 1)
    (n : ℕ) (hn : 0 < n) (epsilon : ℝ) (he0 : 0 < epsilon) (he1 : epsilon < 1)
    (hlarge : 1/Real.sqrt (n : ℝ) < epsilon) :
    productSmoothInner (QAlgorithms.Papers.Independent.Information100.P67.complementaryChannel U) n epsilon ≤
      unassistedBoundary (QAlgorithms.Papers.Independent.Information100.P67.receiverChannel U) n epsilon := by sorry

end QAlgorithms.Papers.Independent.Support50.P04

end
