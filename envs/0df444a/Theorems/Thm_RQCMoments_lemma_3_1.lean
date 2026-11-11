-- Prove2me | Theorems.Thm_RQCMoments_lemma_3_1
-- name    : RQCMoments.lemma_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-11T04:12:48.955282+00:00
-- url     : https://prove2.me/theorems/7be0152a-ba7d-4dc1-902d-4e12e52a4372
-- title:
--   Lemma 3.1 — strong $(p,q)$-designs $\iff$ relative closeness of $\mathbb E|f(U)|^2$
-- statement:
--   Let $\nu$ be a probability distribution on $U(D)$ and let $p,q\ge 0$ be integers. Then $\nu$ is a strong $\varepsilon$-approximate unitary $(p,q)$-design with relative error if and only if, for every polynomial $f$ in the entries of $U$ and $U^*$ whose every monomial contains exactly $p$ entries of $U$ and $q$ entries of $U^*$,
--   $$
--   (1-\varepsilon)\,\mathbb E_{U\sim\mathrm{Haar}(D)}\big[|f(U)|^2\big]\ \le\ \mathbb E_{U\sim\nu}\big[|f(U)|^2\big]\ \le\ (1+\varepsilon)\,\mathbb E_{U\sim\mathrm{Haar}(D)}\big[|f(U)|^2\big].
--   $$
--
--   The lemma turns the operator-level (completely positive) design condition into scalar inequalities for bihomogeneous polynomials; Theorem 3.2 applies it to polynomials in output probabilities.
--
--   **Formalization Note** A polynomial of the stated type is written as $f(U)=\sum_{I,J}c(I,J)\prod_{a=1}^{p}U_{I_a}\prod_{b=1}^{q}\overline{U_{J_b}}$, with $I$ a $p$-tuple and $J$ a $q$-tuple of matrix positions and arbitrary complex coefficients.
--
--   Differences from the source:
--
--   - encoding: polynomial f whose every monomial contains p entries of U and q entries of U* → f(U) = Σ_{I,J} c(I,J) ∏_{a<p} U_{I_a} ∏_{b<q} conj(U_{J_b}), I : Fin p → Fin D × Fin D, J : Fin q → Fin D × Fin D, c arbitrary complex; reason: every such polynomial has this coefficient form and conversely (the paper's (37)); same polynomials
--   - encoding: a probability distribution on U(D) → a Borel probability measure on the subtype Matrix.unitaryGroup (Fin D) ℂ; reason: Lean representation of a distribution on the compact group U(N); same instances
-- source:
--   S.-H. Hung, Random Quantum Circuits Beyond Moment Matching, arXiv:2610.02135 (held version, sha256 079e7da3…), Lemma 3.1, (35), p.18 (PDF p.20)

import Mathlib
import Definitions.Def_RQCMoments_IsStrongDesign

set_option autoImplicit false

open MeasureTheory

namespace RQCMoments

/-- **Lemma 3.1** (Hung, *Random Quantum Circuits Beyond Moment Matching*, arXiv:2610.02135 (held version, sha256 079e7da3…), Lemma 3.1, p.18, PDF p.20).
Let `ν` be a probability distribution on `U(D)` and `p, q` nonnegative integers. Then `ν` is a
strong `ε`-approximate `(p,q)`-design with relative error if and only if for every polynomial `f`
whose every monomial contains `p` entries of `U` and `q` entries of `U*`,
`(1−ε) E_{Haar}|f(U)|² ≤ E_ν|f(U)|² ≤ (1+ε) E_{Haar}|f(U)|²` (35).

**Formalization Note** Such a polynomial is written in coefficient form
`f(U) = ∑_{I,J} c(I,J) ∏_{a<p} U_{I_a} ∏_{b<q} conj(U_{J_b})` with `I : Fin p → [D]×[D]`,
`J : Fin q → [D]×[D]` and arbitrary complex coefficients `c`; every such polynomial has this form
and conversely. -/
theorem lemma_3_1 {D : ℕ} (ν : Measure (Matrix.unitaryGroup (Fin D) ℂ)) [IsProbabilityMeasure ν] (p q : ℕ) (ε : ℝ) :
    IsStrongDesign ν p q ε ↔
      ∀ c : (Fin p → Fin D × Fin D) → (Fin q → Fin D × Fin D) → ℂ,
        let f : Matrix.unitaryGroup (Fin D) ℂ → ℂ := fun U => ∑ I, ∑ J, c I J *
          (∏ a, (U : Matrix (Fin D) (Fin D) ℂ) (I a).1 (I a).2) *
          ∏ b, star ((U : Matrix (Fin D) (Fin D) ℂ) (J b).1 (J b).2)
        (1 - ε) * ∫ U, Complex.normSq (f U) ∂(QAlgorithms.Schur.unitaryHaar D) ≤ ∫ U, Complex.normSq (f U) ∂ν ∧
          ∫ U, Complex.normSq (f U) ∂ν ≤ (1 + ε) * ∫ U, Complex.normSq (f U) ∂(QAlgorithms.Schur.unitaryHaar D) := by sorry

end RQCMoments
