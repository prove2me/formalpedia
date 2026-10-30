-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P29_random_covariant_code_fidelity
-- name    : QAlgorithms.Papers.Independent.Extend50.P29.random_covariant_code_fidelity
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T08:12:19.932854+00:00
-- url     : https://prove2.me/theorems/24d5a9e7-3387-4aa0-a450-a555378b0c7d
-- title:
--   Case 3 / Appendix B: random covariant code fidelity bound, Eq.(7)
-- statement:
--   Let $G$ be finite, $d=|G|\ge1$, and $n\ge3$. Use the left regular action on each $d$-dimensional register. Sample a Haar unit vector $\phi\in\mathcal H_G^{\otimes n}$ and set $\Psi=M\phi$, where $M$ is the explicit invariant-orbit isometry. Reshape $\Psi$ as $E_{z,x}=\sqrt d\,\Psi_{x,z}$, and on the full-rank locus set $T=E(E^\dagger E)^{-1/2}$ and encode by $\rho\mapsto T\rho T^\dagger$. For fixed erased physical mode $1$, use the Appendix B Schmidt decoder, including replacement of that mode by $I/d$. Let $F_{\rm worst}$ be its minimum root fidelity over all normalized logical input states. Then $E^\dagger E$ is positive definite almost surely, and
--   $$\Pr\!\left[F_{\rm worst}<1-d^{(9-2n)/8}\right]\le\exp\!\left[-\frac{d^2}{216}\left(d^{(2n-8)/4}-432\log\left(30d^{(7+2n)/8}\right)\right)\right].$$
--   The probability is evaluated on the full-rank locus with its original, unrenormalized Haar law. Real powers and the natural logarithm are used. This is a fixed-erasure estimate, with no simultaneous minimum over erased sites.
--
--   **Formalization Note** The code uses $n=r+2$, $r\ge1$, and the equivalent recovered-channel formula from Appendix B. The printed B8 proof's unresolved prefactor issue is recorded in the audit.
-- source:
--   Error Correction of Quantum Reference Frame Information, arXiv:1709.04471v1, PDF p. 5, Case 3 / Appendix B: random covariant code fidelity bound, Eq.(7)

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P29

noncomputable section

open MeasureTheory MeasureTheory.Measure

open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.L2Operator

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Extend50.P29

open QAlgorithms.Papers.Independent.Information100.P32 (evolution)

open QAlgorithms.Papers.Independent.Next46.P39 (inverseSqrt rectAct)

open QAlgorithms.Papers.Independent.Support21.P09 (groupLeftRegular)

/-- PDF p.5, Eq.(7), with Appendix B pp.8--13: the exact printed strict
failure event for the Haar-orbit/polar construction. Here n=r+2≥3, the domain
of the Schmidt decoder using physical modes 2 and 3. The n≥5 condition on p.5
concerns asymptotic usefulness, not the domain of Eq.(7). The law on
the full-rank locus is NOT renormalized; full rank almost surely is a conclusion.
This is a fixed erased output, not a simultaneous bound over n erasures.
The reversed event printed at the end of p.13 is corrected using p.5. -/
theorem random_covariant_code_fidelity
    (G : Type) [Group G] [Fintype G] (r : ℕ) (hr : 1 ≤ r) :
    let d : ℝ := Fintype.card G
    let n : ℝ := (r : ℝ) + 2
    ((invariantSampleLaw G (r + 2)) {φ |
      ((reshapedEncoder (randomInvariant (r + 2) φ))ᴴ *
        reshapedEncoder (randomInvariant (r + 2) φ)).PosDef}) = 1 ∧
    ((invariantSampleLaw G (r + 2)) {φ |
      ((reshapedEncoder (randomInvariant (r + 2) φ))ᴴ *
        reshapedEncoder (randomInvariant (r + 2) φ)).PosDef ∧
      worstRootFidelity (pairMarginal (randomInvariant (r + 2) φ)) <
        1 - Real.rpow d ((9 - 2 * n) / 8)}).toReal ≤
      Real.exp (-(d ^ 2 / 216) *
        (Real.rpow d ((2 * n - 8) / 4) -
          432 * Real.log (30 * Real.rpow d ((7 + 2 * n) / 8)))) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P29

end
