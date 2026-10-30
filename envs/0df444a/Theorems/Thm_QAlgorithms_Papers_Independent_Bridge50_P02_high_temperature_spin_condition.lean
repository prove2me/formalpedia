-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P02_high_temperature_spin_condition
-- name    : QAlgorithms.Papers.Independent.Bridge50.P02.high_temperature_spin_condition
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T11:45:59.914005+00:00
-- url     : https://prove2.me/theorems/5dffa702-0da4-4d2a-9c38-de2dceb01d41
-- title:
--   Proposition 2: high-temperature spin Gibbs states satisfy Condition 1
-- statement:
--   Let $d\ge1$ be an integer and let the common one-site Hilbert space have finite dimension $q\ge1$. Let $\Phi,\Psi$ be translation-invariant self-adjoint interactions on $\mathbb Z^d$, with zero empty-support terms and finite ranges in Manhattan distance. Local observables are included by tensoring with identities. For $\Lambda_n=\{-n,\ldots,n\}^d$, let $H^\Phi_{\Lambda_n}=\sum_{X\subseteq\Lambda_n}\Phi_X$, and similarly for $\Psi$. There exists $b>0$, depending on the two interactions, $d$, and the site space, such that for every $0<\beta_1,\beta_2<b$, the states
--   $$\rho_n=\frac{e^{-\beta_1H^\Phi_{\Lambda_n}}}{\operatorname{Tr}e^{-\beta_1H^\Phi_{\Lambda_n}}},\qquad\sigma_n=\frac{e^{-\beta_2H^\Psi_{\Lambda_n}}}{\operatorname{Tr}e^{-\beta_2H^\Psi_{\Lambda_n}}}$$
--   satisfy Condition 1 with $w_n=|\Lambda_n|=(2n+1)^d$.
--
--   Condition 1 means one common analytic disc for their Petz log-overlaps, finite normalized real limits, and a bound uniform in $n$ and the disc. No numeric temperature threshold is asserted.
-- source:
--   Second-order asymptotics for quantum hypothesis testing in settings beyond i.i.d. - quantum lattice systems and more, arXiv:1510.04682v4, PDF p. 18, Proposition 2

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P02

noncomputable section

open Filter MeasureTheory

open scoped BigOperators ENNReal Matrix ComplexConjugate ComplexOrder Matrix.Norms.L2Operator Topology

namespace QAlgorithms.Papers.Independent.Bridge50.P02

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Claimed50.P15
  (evaluate positiveMatrixRpow modularMatrix modularQuadratic resolventOverlap petzOverlap
    finiteRelativeEntropyNats)

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower SupportIncluded)

open QAlgorithms.Papers.Independent.Information100.P63 (Mat tensorPower testingBeta)

open QAlgorithms.Papers.Independent.Information100.P58 (normalQuantile)

variable {I : Type} [Fintype I] [DecidableEq I]

/-- Proposition 2, PDF p.18: a temperature threshold uniform in both temperatures and n.
The threshold may depend on d, the site dimension, and both interactions. -/
theorem high_temperature_spin_condition (d q : ℕ) (hd : 1 ≤ d) (hq : 0 < q)
    (Phi Psi : SpinInteraction d q)
    (hPhiTranslation : TranslationInvariant Phi) (hPsiTranslation : TranslationInvariant Psi)
    (hPhiRange : FiniteRange Phi) (hPsiRange : FiniteRange Psi) :
    ∃ b : ℝ, 0 < b ∧ ∀ beta1 beta2 : ℝ,
      0 < beta1 → beta1 < b → 0 < beta2 → beta2 < b →
        ConditionOne (spinSequence Phi Psi beta1 beta2) (spinVolumeWeight d) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P02

end
