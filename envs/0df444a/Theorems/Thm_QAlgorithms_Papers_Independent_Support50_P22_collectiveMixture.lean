-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P22_collectiveMixture
-- name    : QAlgorithms.Papers.Independent.Support50.P22.collectiveMixture
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T20:51:51.636982+00:00
-- url     : https://prove2.me/theorems/9595a0ac-a8bf-41fd-a1f3-5c779047a3ac
-- title:
--   Collective-input mixture bound (5)
-- statement:
--   Let $d\ge1$, $n\ge0$, and $K\cong H$. Let $E$ be a finite-dimensional classical-output CPTP QKD map with variable key length and complete public transcript, and let $F=S\circ E$ be its length- and transcript-preserving ideal key replacement. Let $\bar\epsilon\ge0$. Suppose that for every normalized pure density $\sigma_{HK}$,
--   $$
--   \|((E-F)\otimes\operatorname{id}_{K^n})(\sigma_{HK}^{\otimes n})\|_1\le\bar\epsilon.
--   $$
--   Then the maximum over these pure states is attained and, for the mixed Haar extension $\tau_{H^nK^n}$,
--   $$
--   \|((E-F)\otimes\operatorname{id}_{K^n})(\tau_{H^nK^n})\|_1
--   \le\max_{\sigma_{HK}\ \mathrm{pure}}
--   \|((E-F)\otimes\operatorname{id}_{K^n})(\sigma_{HK}^{\otimes n})\|_1
--   \le\bar\epsilon.
--   $$
--   The maximum ranges over all unit vectors modulo the irrelevant phase of their densities. This transfers the collective-input bound to the mixed extension while retaining the adversary's $K^n$ register.
-- source:
--   Post-selection technique for quantum channels with applications to quantum cryptography, arXiv:0809.3019v1, PDF p. 3, Unnumbered collective-input mixture bound, equation (5)

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P22

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.L2Operator

open MeasureTheory

namespace QAlgorithms.Papers.Independent.Support50.P22

attribute [local instance] Classical.decEq Classical.propDecidable

open QAlgorithms.Papers.Independent.Gap48.P20 (Copies)

open QAlgorithms.Papers.Independent.Information100.P69 (diamond)

open QAlgorithms.Papers.Independent.Dependency50.P18 (ClassicalOutput)

attribute [local instance] QAlgorithms.Papers.Independent.Support50.P22.postselectionMatrixMeasurableSpace

attribute [local instance] QAlgorithms.Papers.Independent.Support50.P22.postselectionMatrixBorelSpace

/-- Collective-input mixture bound, equation (5), PDF p.3. A maximizing pure
state is attained and dominates EVERY pure input, retaining the entire max
chain without an empty or unbounded real supremum. This input is the mixed
Haar extension, not its purification with an additional N. -/
theorem collectiveMixture (n d : ℕ) (hd : 0 < d)
    {L C : Type} [Fintype L] [DecidableEq L] [Nonempty L]
    [Fintype C] [DecidableEq C] [Nonempty C]
    (len : L → ℕ)
    (E : Matrix (Copies (Fin d) n) (Copies (Fin d) n) ℂ →ₗ[ℂ]
      Matrix (KeyOut L C len) (KeyOut L C len) ℂ)
    (hE : IsChannel E) (hclass : ClassicalOutput E)
    (epsilonBar : ℝ) (hepsilon : 0 ≤ epsilonBar)
    (hcollective : ∀ phi : EuclideanSpace ℂ (Fin d × Fin d), IsState phi →
      traceNorm (tensorId (E - idealProtocol len E)
        (pairedPower n d (pureDensity phi))) ≤ epsilonBar) :
    ∃ phiMax : EuclideanSpace ℂ (Fin d × Fin d), IsState phiMax ∧
      (∀ phi : EuclideanSpace ℂ (Fin d × Fin d), IsState phi →
        traceNorm (tensorId (E - idealProtocol len E) (pairedPower n d (pureDensity phi))) ≤
        traceNorm (tensorId (E - idealProtocol len E) (pairedPower n d (pureDensity phiMax)))) ∧
      traceNorm (tensorId (E - idealProtocol len E) (tauPair n d hd)) ≤
        traceNorm (tensorId (E - idealProtocol len E) (pairedPower n d (pureDensity phiMax))) ∧
      traceNorm (tensorId (E - idealProtocol len E) (pairedPower n d (pureDensity phiMax))) ≤
        epsilonBar := by sorry

end QAlgorithms.Papers.Independent.Support50.P22

end
