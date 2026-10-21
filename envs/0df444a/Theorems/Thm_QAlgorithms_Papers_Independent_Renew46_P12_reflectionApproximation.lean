-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P12_reflectionApproximation
-- name    : QAlgorithms.Papers.Independent.Renew46.P12.reflectionApproximation
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T20:12:39.910966+00:00
-- url     : https://prove2.me/theorems/836aac87-932e-4700-a5f5-b1ea5bbb5213
-- title:
--   Dyadic approximation of reflections, with the two-zero-coordinate improvement
-- statement:
--   There is an absolute constant $B>0$ such that, for every $n\ge1$ and $0<\varepsilon\le1$, one can choose a nonnegative integer m, independently of the vector below, with
--
--   $$
--   \left\lceil\frac n2\right\rceil\le m\le\left\lceil\frac n2\right\rceil+B\bigl(1+\log_2(1/\varepsilon)\bigr).
--   $$
--
--   For every normalized vector $|\psi\rangle$ on n qubits, the following assertions hold. All approximating vectors mentioned here are normalized, and each of their coordinates has the form $(a+b\sqrt2+ci+di\sqrt2)/2^m$ with integers a,b,c,d that may vary by coordinate.
--
--   1. There are vectors $|\phi_0\rangle,|\phi_1\rangle$ on one extra qubit and the original register such that
--
--   $$
--   \|R_{\phi_0}R_{\phi_1}-I_2\otimes R_\psi\|_{\mathrm{Fr}}\le\varepsilon.
--   $$
--
--   2. If two distinct computational-basis coordinates of $|\psi\rangle$ vanish, there is a vector $|\phi\rangle$ on the original register such that
--
--   $$
--   \|R_\phi-R_\psi\|_{\mathrm{Fr}}\le\varepsilon.
--   $$
--
--   Here $R_v=I-2|v\rangle\langle v|$. The first bound compares full operators on both ancillary sectors; the second uses no ancillary qubit. This is an arithmetic approximation guarantee for reflection operators.
--
--   **Formalization Note** The additive 1 in the logarithmic overhead retains integer rounding at $\varepsilon=1$, consistent with the explicit constant overhead on PDF p.3.
-- source:
--   Synthesis of unitaries with Clifford+T circuits, arXiv:1306.3200v1, PDF p. 2, Lemma 3 (proof continues on PDF p.3)

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P12

namespace QAlgorithms.Papers.Independent.Renew46.P12

noncomputable section

/-- Lemma 3, PDF pp.2–3, both clauses. The exponent is uniform over normalized psi.
General case: two arithmetic reflections approximate the full I_2 tensor R_psi.
Two-zero-coordinate case: one reflection on the original register suffices.
The additive 1 in the logarithmic overhead records integer rounding at eps=1;
this is the source's asymptotic claim, with its explicit p.3 choice including +5.
The existential conclusion does not depend on the proof's defective signed floor
rounding: truncation toward zero restores the required nonnegative four-square deficit.
This proof correction and the endpoint corrections require independent moderation. -/
theorem reflectionApproximation :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
      ∀ eps : ℝ, 0 < eps → eps ≤ 1 →
      ∃ m : ℕ, (n + 1) / 2 ≤ m ∧
        (m : ℝ) ≤ (((n + 1) / 2 : ℕ) : ℝ) +
          C * (1 + Real.log (1 / eps) / Real.log 2) ∧
      ∀ psi : EuclideanSpace ℂ (Qubits n), IsState psi →
        (∃ phi0 phi1 : EuclideanSpace ℂ (Bool × Qubits n),
          IsState phi0 ∧ IsState phi1 ∧
          (∀ z, HasDenominator 2 m (phi0 z)) ∧
          (∀ z, HasDenominator 2 m (phi1 z)) ∧
          frobNorm (householderReflection phi0 * householderReflection phi1 - identityExtension (householderReflection psi)) ≤ eps) ∧
        ((∃ j l : Qubits n, j ≠ l ∧ psi j = 0 ∧ psi l = 0) →
          ∃ phi : EuclideanSpace ℂ (Qubits n), IsState phi ∧
            (∀ z, HasDenominator 2 m (phi z)) ∧
            frobNorm (householderReflection phi - householderReflection psi) ≤ eps) := by sorry

end

end QAlgorithms.Papers.Independent.Renew46.P12
