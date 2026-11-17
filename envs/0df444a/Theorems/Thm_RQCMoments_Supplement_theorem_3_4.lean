-- Prove2me | Theorems.Thm_RQCMoments_Supplement_theorem_3_4
-- name    : RQCMoments.Supplement.theorem_3_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T07:49:04.749112+00:00
-- url     : https://prove2.me/theorems/d4c9ce09-832d-41a5-be71-f9020e6fc432
-- title:
--   Theorem 3.4 — closeness of $\mathbb E|f(U)|^2$ for polynomials of degree $\le(p,q)$ implies a strong $\varepsilon$-approximate $(p,q)$-design
-- statement:
--   Let $D\ge1$ be an integer and $\nu$ a probability distribution on the unitary group $U(D)$. Suppose that for every polynomial $f$ in the entries of $U$ and of $U^*$ (the entrywise conjugate) whose every monomial contains at most $p$ entries of $U$ and at most $q$ entries of $U^*$,
--
--   $$(1-\varepsilon)\,\mathbb E_{U\sim\mathrm{Haar}(D)}\big[|f(U)|^2\big]\le\mathbb E_{U\sim\nu}\big[|f(U)|^2\big]\le(1+\varepsilon)\,\mathbb E_{U\sim\mathrm{Haar}(D)}\big[|f(U)|^2\big].$$
--
--   Then $\nu$ is a strong $\varepsilon$-approximate $(p,q)$-design.
--
--   This is the form of the design criterion used to certify the constructions of Section 5: one only has to compare second moments of polynomials, possibly of mixed degrees.
--
--   **Formalization Note** A polynomial with at most $p$ entries of $U$ and $q$ of $U^*$ per monomial is written in coefficient form $\sum_{r\le p}\sum_{s\le q}\sum_{I,J}c(r,s,I,J)\prod_{a<r}U_{I_a}\prod_{b<s}\overline{U_{J_b}}$ with arbitrary complex coefficients; every such polynomial has this form. "Strong $\varepsilon$-approximate $(p,q)$-design" is the published `RQCMoments.IsStrongDesign`. $\varepsilon$ is any real number, as printed.
--
--   Differences from the source:
--
--   - encoding: polynomial whose monomials contain at most p entries of U and at most q of U* → coefficient form ∑_{r≤p} ∑_{s≤q} ∑_{I,J} c(r,s,I,J) ∏ U_{I_a} ∏ conj(U_{J_b}) with arbitrary complex c; reason: every such polynomial has this form and conversely
-- source:
--   S.-H. Hung, Random Quantum Circuits Beyond Moment Matching, arXiv:2610.02135 (held version, sha256 079e7da3…), Theorem 3.4, (47), p.20 (PDF p.22)

import Mathlib
import Definitions.Def_RQCMoments_IsStrongDesign

set_option autoImplicit false

open MeasureTheory

namespace RQCMoments

namespace Supplement

/-- **Theorem 3.4** (Hung, *Random Quantum Circuits Beyond Moment Matching*, arXiv:2610.02135 (held version, sha256 079e7da3…), Theorem 3.4, (47), p.20, PDF p.22).
For an integer `D ≥ 1`, let `ν` be a unitary distribution on `U(D)`. If for every polynomial `f`
whose every monomial contains at most `p` entries of `U` and at most `q` entries of `U*`,
`(1 − ε) E_{Haar}|f(U)|² ≤ E_ν|f(U)|² ≤ (1 + ε) E_{Haar}|f(U)|²` (47), then `ν` is a strong
`ε`-approximate `(p,q)`-design.

**Formalization Note** Such a polynomial is written in coefficient form
`f(U) = ∑_{r ≤ p} ∑_{s ≤ q} ∑_{I,J} c(r,s,I,J) ∏_{a<r} U_{I_a} ∏_{b<s} conj(U_{J_b})` with
`I : Fin r → [D]×[D]`, `J : Fin s → [D]×[D]` and arbitrary complex coefficients; every polynomial
whose monomials have at most `p` entries of `U` and at most `q` of `U*` has this form, and
conversely. "Unitary distribution" is a probability measure on `U(D)` (published Borel σ-algebra);
`ε` is any real number, as printed. -/
theorem theorem_3_4 {D : ℕ} (hD : 1 ≤ D) (ν : Measure (Matrix.unitaryGroup (Fin D) ℂ))
    [IsProbabilityMeasure ν] (p q : ℕ) (ε : ℝ)
    (h : ∀ c : (r : Fin (p + 1)) → (s : Fin (q + 1)) →
        (Fin r.val → Fin D × Fin D) → (Fin s.val → Fin D × Fin D) → ℂ,
      let f : Matrix.unitaryGroup (Fin D) ℂ → ℂ := fun U => ∑ r, ∑ s, ∑ I, ∑ J, c r s I J *
        (∏ a, (U : Matrix (Fin D) (Fin D) ℂ) (I a).1 (I a).2) *
        ∏ b, star ((U : Matrix (Fin D) (Fin D) ℂ) (J b).1 (J b).2)
      (1 - ε) * ∫ U, Complex.normSq (f U) ∂(QAlgorithms.Schur.unitaryHaar D) ≤
          ∫ U, Complex.normSq (f U) ∂ν ∧
        ∫ U, Complex.normSq (f U) ∂ν ≤
          (1 + ε) * ∫ U, Complex.normSq (f U) ∂(QAlgorithms.Schur.unitaryHaar D)) :
    IsStrongDesign ν p q ε := by sorry

end Supplement

end RQCMoments
