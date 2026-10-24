-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P04_erasure_exact_and_expansion
-- name    : QAlgorithms.Papers.Independent.Support50.P04.erasure_exact_and_expansion
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T18:28:09.8833+00:00
-- url     : https://prove2.me/theorems/f01d4815-e3e8-427b-96f7-f8181df9c7e8
-- title:
--   Erasure cpp coding: exact integer-message fidelity and normal approximation
-- statement:
--   Let $\mathcal N:A\to B$ be a CPTP channel on finite positive-dimensional complex Hilbert spaces with fixed orthonormal bases. Write $\widehat R(n;\varepsilon)$ and $\widehat R^{\mathrm{cpp}}(n;\varepsilon)$ for the maximum unassisted and classical-post-processing assisted entanglement-transmission rates. A code has a positive integer message dimension $M$, rate $\log_2 M/n$, and squared fidelity to the normalized maximally entangled target at least $1-\varepsilon$. A cpp encoder may retain sender memory; its decoder is LOCC across that memory and the receiver outputs, with its final quantum output at the receiver and no preshared entanglement. For the pure-flag qubit erasure channel $\mathcal E_\beta(X)=(1-\beta)X\oplus\beta\operatorname{tr}(X)|e\rangle\langle e|$, with $0\le\beta\le1$, every integer $n,M\ge1$ has optimal cpp squared fidelity
--
--   $$F_{\mathrm{opt}}(n,M)=\sum_{l=0}^n\binom nl\beta^l(1-\beta)^{n-l}\min\left\{1,\frac{2^{n-l}}M\right\}.$$
--
--   An actual cpp code with this message dimension attains this value. Fix $0<\varepsilon<1$. All logarithms are binary and $\Phi^{-1}$ is the standard Gaussian quantile. Remainder constants may depend on the fixed channel and error, and are chosen before the block length: there are $C>0$ and $n_0\ge2$ such that the displayed bound holds for every integer $n\ge n_0$. If $0<\beta<1$, then
--
--   $$\left|\widehat R_{\mathcal E_\beta}^{\mathrm{cpp}}(n;\varepsilon)-1+\beta-\sqrt{\beta(1-\beta)/n}\,\Phi^{-1}(\varepsilon)\right|\le C/n.$$
--
--   The finite-block formula retains both channel endpoints and integer-message rounding.
-- source:
--   Quantum Coding with Finite Resources, arXiv:1504.04617v2, PDF p. 6, Result 2, Eqs. (8)–(9), (69)–(70)

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P04

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open QAlgorithms

namespace QAlgorithms.Papers.Independent.Support50.P04

variable {A B E : Type} [Fintype A] [DecidableEq A]

variable [Fintype B] [DecidableEq B] [Fintype E] [DecidableEq E]

/-- arXiv:1504.04617v2, PDF pp.5–6,18–19, Result 2, Eqs.(8)–(9),(69)–(70).
Printed Eq.(8) is an inversion shorthand; changed to exact fixed-INTEGER-M
optimal fidelity and attainment. Integer rounding need not saturate epsilon.
Only the Gaussian clause excludes beta=0,1; the exact clause includes them. -/
theorem erasure_exact_and_expansion (beta : ℝ) (hb0 : 0 ≤ beta) (hb1 : beta ≤ 1) :
    (∀ n M : ℕ, 0 < n → 0 < M →
      optimalCppFidelity (QAlgorithms.Papers.Independent.Renew46.P36.flaggedErasure (A := Fin 2) beta) n M = (erasureFidelityFormula beta n M : EReal) ∧
      ∃ C : CppCode (Fin n → Fin 2) (Fin n → Option (Fin 2)),
        C.M = M ∧ cppFidelity (piSuperop (fun _ : Fin n => (QAlgorithms.Papers.Independent.Renew46.P36.flaggedErasure (A := Fin 2) beta))) C = erasureFidelityFormula beta n M) ∧
    (0 < beta → beta < 1 → ∀ epsilon : ℝ, 0 < epsilon → epsilon < 1 →
      constantRemainderExpansion (fun n => cppBoundary (QAlgorithms.Papers.Independent.Renew46.P36.flaggedErasure (A := Fin 2) beta) n epsilon)
        (1-beta) (beta*(1-beta)) epsilon) := by sorry

end QAlgorithms.Papers.Independent.Support50.P04

end
