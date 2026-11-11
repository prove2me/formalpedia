-- Prove2me | Theorems.Thm_QuantumXoP_Security_theorem_3_1
-- name    : QuantumXoP.Security.theorem_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T21:05:47.919453+00:00
-- url     : https://prove2.me/theorems/cf66a00f-9a68-4bd3-93ef-ea2dc4924bf1
-- title:
--   Theorem 3.1 — Fourier expansion of functionals
-- statement:
--   Let $H:F_n\to\mathbb C$ be a functional. Then
--   $$H(f)=\sum_{\gamma\in\widehat F}\widehat H(\gamma)\,\chi_\gamma(f)\quad\text{for every }f,\qquad \widehat H(\gamma)=\langle\chi_\gamma,H\rangle=\mathbb E_{f\leftarrow F}\big[\overline{\chi_\gamma(f)}\,H(f)\big].$$
--
--   The characters form an orthonormal basis of the functionals; every later computation of $\mu_{XoP[r]}$ is carried out in this basis.
--
--   Differences from the source:
--   - generalization: n is a fixed positive integer (§2, p. 8) → every n : ℕ, including n = 0; reason: the case n = 0 is one extra instance; the statement specializes to every n ≥ 1
-- source:
--   Wonseok Choi, Minki Hhan, Junyoung Jang, Quantum Security of XOR of Permutations via Fourier Analysis, STOC 2027 submission #815 (October 2026), p. 9 (PDF p. 11), Theorem 3.1

import Mathlib
import Definitions.Def_QuantumXoP_Security_Fourier

namespace QuantumXoP.Security

open QAlgorithms
open scoped ComplexConjugate

/-- Theorem 3.1 (p. 9): Fourier expansion of functionals. -/
theorem theorem_3_1 {n : ℕ} (H : Fn n → ℂ) :
    (∀ f : Fn n, H f = ∑ γ : Fn n, fourierCoeff H γ * chi γ f) ∧
    (∀ γ : Fn n, fourierCoeff H γ =
      ((Fintype.card (Fn n) : ℂ))⁻¹ * ∑ f : Fn n, conj (chi γ f) * H f) := by sorry

end QuantumXoP.Security
