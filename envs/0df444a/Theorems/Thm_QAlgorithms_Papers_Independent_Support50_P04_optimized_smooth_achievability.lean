-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P04_optimized_smooth_achievability
-- name    : QAlgorithms.Papers.Independent.Support50.P04.optimized_smooth_achievability
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T18:38:43.199821+00:00
-- url     : https://prove2.me/theorems/0baf6e14-0c5a-46f8-84a8-859f33e01c55
-- title:
--   Optimized smooth-min-entropy achievability
-- statement:
--   Let $\mathcal N:A\to B$ be a CPTP channel on finite positive-dimensional complex Hilbert spaces with fixed orthonormal bases. Write $\widehat R(n;\varepsilon)$ and $\widehat R^{\mathrm{cpp}}(n;\varepsilon)$ for the maximum unassisted and classical-post-processing assisted entanglement-transmission rates. A code has a positive integer message dimension $M$, rate $\log_2 M/n$, and squared fidelity to the normalized maximally entangled target at least $1-\varepsilon$. A cpp encoder may retain sender memory; its decoder is LOCC across that memory and the receiver outputs, with its final quantum output at the receiver and no preshared entanglement. Fix $n\ge1$, $0<\varepsilon<1$, and one isometry $U:A\hookrightarrow B\otimes E$; $\mathcal N$ and $\mathcal N^c$ are respectively the receiver and environment partial traces of that same dilation. For a normalized center $\omega$, define $H_{\min}^{\delta}(A|E)_\omega$ as the supremum of real $\lambda$ for which there exist $\bar\omega\succeq0$ of trace at most one and a normalized density $\sigma_E$ such that $F(\bar\omega,\omega)\ge1-\delta^2$ and $\bar\omega\preceq2^{-\lambda}I_A\otimes\sigma_E$. Supremums are taken in the extended reals. For every normalized input $\rho$ on $A^n$, put $\omega^\rho=(\mathrm{id}\otimes(\mathcal N^c)^{\otimes n})(\psi^\rho)$. Then
--
--   $$\widehat R(n;\varepsilon)\ge\sup_{0<\eta<\varepsilon}\sup_{\rho\in\mathcal S(A^n)}\frac{H_{\min}^{\sqrt{\varepsilon-\eta}}(A^n|E^n)_{\omega^\rho}-4\log_2(1/\eta)-1}{n}.$$
--
--   The one-bit term accounts for integer message rounding.
-- source:
--   Quantum Coding with Finite Resources, arXiv:1504.04617v2, PDF p. 14, Corollary 5, Eq. (46)

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P04

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open QAlgorithms

namespace QAlgorithms.Papers.Independent.Support50.P04

variable {A B E : Type} [Fintype A] [DecidableEq A]

variable [Fintype B] [DecidableEq B] [Fintype E] [DecidableEq E]

/-- arXiv:1504.04617v2, PDF pp.13–14, Corollary 5, Eq.(46).
Printed ball F>=(1-delta)^2; changed to F>=1-delta^2 to match the named purified
distance and the square-root conversion used in (45),(51). Entire expression /n. -/
theorem optimized_smooth_achievability [Nonempty A] [Nonempty B] [Nonempty E]
    (U : Matrix (B × E) A ℂ) (hU : Uᴴ * U = 1)
    (n : ℕ) (hn : 0 < n) (epsilon : ℝ) (he0 : 0 < epsilon) (he1 : epsilon < 1) :
    smoothInner (QAlgorithms.Papers.Independent.Information100.P67.complementaryChannel U) n epsilon ≤
      unassistedBoundary (QAlgorithms.Papers.Independent.Information100.P67.receiverChannel U) n epsilon := by sorry

end QAlgorithms.Papers.Independent.Support50.P04

end
