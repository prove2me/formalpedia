-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P05_twirled_marginals_depolarizing
-- name    : QAlgorithms.Papers.Independent.Extend50.P05.twirled_marginals_depolarizing
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T13:23:45.26115+00:00
-- url     : https://prove2.me/theorems/851648de-d0a5-496e-b44a-576b62042f42
-- title:
--   Depolarizing marginals and constant pure-input fidelity
-- statement:
--   Let $d\ge2$, $N\ge1$ and let $T:M_d\to M_d^{\otimes N}$ be a CPTP map. For its explicit normalized-Haar twirl $\widetilde T$, there are real numbers $p_i\in[-1/(d^2-1),1]$, independent of the input, such that $\widetilde T_i=D_{p_i}$. For every normalized pure input $\psi$,
--
--   $$
--   \langle\psi|\widetilde T_i(|\psi\rangle\langle\psi|)|\psi\rangle
--   =p_i+\frac{1-p_i}{d}.
--   $$
--
--   The infimum over normalized pure inputs and the normalized Haar average both equal this same number for every marginal $i$.
--
--   This reduction supplies the input-independent quality parameters used in the cloning region. It makes no constant-fidelity assertion for arbitrary mixed inputs.
-- source:
--   A geometrical description of the universal $1 \to 2$ asymmetric quantum cloning region, arXiv:2106.09655v1, PDF p. 6, Unnumbered reduction: depolarizing marginals and constant pure-input fidelity

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P05

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.Elementwise

open MeasureTheory

namespace QAlgorithms.Papers.Independent.Extend50.P05

open QAlgorithms.Papers.Independent.Information100.P34 (choi)

open QAlgorithms.Papers.Independent.Information100.P60 (isotropic)

open QAlgorithms.Papers.Independent.Information100.P63 (tensorPower)

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

/-- PDF p.6: every marginal of the actual Haar twirl is depolarizing, with input-independent
shrink factor in its CPTP range, and its worst and average pure-input fidelities coincide. -/
theorem twirled_marginals_depolarizing (d N : ℕ) (hd : 2 ≤ d) (hN : 1 ≤ N)
    (T : Superop (Fin d) (CloningOutputs d N)) (hT : IsChannel T) :
    ∃ p : Fin N → ℝ, ∀ i,
      (-(1 : ℝ) / ((d : ℝ) ^ 2 - 1) ≤ p i ∧ p i ≤ 1) ∧
      cloningMarginal (cloningTwirl T) i = depolarizingShrink d (p i) ∧
      (∀ psi : EuclideanSpace ℂ (Fin d), IsState psi →
        pureInputFidelity (cloningMarginal (cloningTwirl T) i) psi = p i + (1 - p i) / (d : ℝ)) ∧
      worstMarginal (cloningTwirl T) i = p i + (1 - p i) / (d : ℝ) ∧
      QuditFidelity.averageFidelity d (by omega) (cloningMarginal (cloningTwirl T) i) =
        p i + (1 - p i) / (d : ℝ) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P05

end
