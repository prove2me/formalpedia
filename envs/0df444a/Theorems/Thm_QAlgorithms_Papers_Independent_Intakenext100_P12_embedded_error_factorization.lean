-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P12_embedded_error_factorization
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P12.embedded_error_factorization
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T23:48:30.383333+00:00
-- url     : https://prove2.me/theorems/67915e97-d7cc-4f3f-bbef-a03e1f88ef35
-- title:
--   §V (40)–(43): exact correctable embedded-error factorization
-- statement:
--   Let $n\ge1$, $\alpha>0$, and $C=\{(u,v):|u|<\alpha/2,\ |v|<\pi/(n\alpha)\}$. For $c\in\mathbb C^n$ and an $L^2$ error function $\eta$ supported almost everywhere in $C$, define the physical wavefunction by (40), using the explicitly fixed factor $\sqrt{n\alpha/(2\pi)}$ in the comb integral. This wavefunction is in $L^2(\mathbb R)$, and an isometric realization of the logical/syndrome tensor space exists. For any two such pairs,
--
--   $$\langle\psi_1,\psi_2\rangle=\left(\sum_j\overline{c_{1j}}c_{2j}\right)\int_C\overline{\eta_1(u,v)}\eta_2(u,v)\,du\,dv.$$
--
--   In particular unit logical and error vectors produce a unit physical vector, and separating the syndrome preserves the logical factor. The logical inner product is the ordinary finite one, not a norm on an ideal delta comb.
-- source:
--   Encoding a qubit in an oscillator, arXiv:quant-ph/0008040v3, PDF p. 7, §V (40)–(43): exact correctable embedded-error factorization

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P12

noncomputable section

open scoped BigOperators

open MeasureTheory Matrix ComplexConjugate

open QAlgorithms.Papers.Independent.Dependency50.P10 (Phase sigma)

namespace QAlgorithms.Papers.Independent.Intakenext100.P12

/-- Section V (40)–(43), PDF p.7: the constructed physical realization preserves the
logical/error tensor inner product. Isometry and nonzero realization are conclusions. -/
theorem embedded_error_factorization (n : ℕ) (hn : 0 < n) (alpha : ℝ) (ha : 0 < alpha) :
    HasExactRealization n alpha ∧
    (∀ (c : Fin n → ℂ) (eta : (ℝ × ℝ) → ℂ), SupportedError n alpha eta →
      MemLp (embeddedWave n alpha c eta) 2 volume) ∧
    (∀ (c1 c2 : Fin n → ℂ) (eta1 eta2 : (ℝ × ℝ) → ℂ),
      SupportedError n alpha eta1 → SupportedError n alpha eta2 →
      (∫ q : ℝ, conj (embeddedWave n alpha c1 eta1 q) * embeddedWave n alpha c2 eta2 q) =
        finiteInner c1 c2 * ∫ uv : ℝ × ℝ, conj (eta1 uv) * eta2 uv) ∧
    (∀ (c : Fin n → ℂ) (eta : (ℝ × ℝ) → ℂ),
      SupportedError n alpha eta → finiteInner c c = 1 →
      (∫ uv : ℝ × ℝ, ‖eta uv‖ ^ 2) = 1 →
      (∫ q : ℝ, ‖embeddedWave n alpha c eta q‖ ^ 2) = 1) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P12

end
