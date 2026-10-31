-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P82_asymptotic_additivity_characterizations
-- name    : QAlgorithms.Papers.Independent.Intake100.P82.asymptotic_additivity_characterizations
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T15:25:49.479994+00:00
-- url     : https://prove2.me/theorems/03b61fcf-58d4-4f1b-be4b-95ea55109539
-- title:
--   Theorem 6.1: all eight conditions for asymptotic additivity
-- statement:
--   Let $M$ be a nonempty compact metric space with its Borel sigma-algebra, and let $\varphi:M\to M$ be continuous. Write $\mathcal P(M)$ for Borel probabilities with the weak topology, $\mathcal P_\varphi(M)$ for invariant probabilities, and $\mathcal E_\varphi(M)$ for ergodic probabilities. Entropy $h_\varphi$ is Kolmogorov–Sinai entropy with natural logarithms. For a bounded Borel sequence $\mathcal G=(G_n)_{n\ge1}$, asymptotic additivity means uniform approximation at linear scale by sums $S_n g=\sum_{j=0}^{n-1}g\circ\varphi^j$ of continuous functions. For such a sequence, $\mathcal G(Q)$ denotes the constructed real limit of $n^{-1}\int G_n\,dQ$ on invariant probabilities, and $p(\mathcal G)$ denotes its topological pressure. All time limits use positive integers.
--
--   For $\mathcal G=(G_n)\subset B(M)$, write TV for tempered variation (the small-radius limit of the normalized absolute Bowen oscillation). Write WAA for
--   $$|G_{m+n}-G_m-G_n\circ\varphi^m|\le C_m,\qquad C_m/m\to0.$$
--   Write SB for the self-block condition
--   $$\lim_{k\to\infty}\limsup_{n\to\infty}\frac1n\|G_n-k^{-1}S_nG_k\|_\infty=0.$$
--   All eight assertions hold:
--
--   1. Continuous additive sequences are AA.
--   2. Bounded Borel additive sequences with TV are AA.
--   3. WAA sequences with every term continuous are AA.
--   4. WAA sequences with TV are AA.
--   5. If every $G_n$ is continuous, AA is equivalent to SB.
--   6. For bounded Borel terms, AA is equivalent to TV and SB together.
--   7. AA is equivalent to TV together with bounded Borel approximants $f_k$ satisfying $\lim_k\limsup_n n^{-1}\|G_n-S_nf_k\|_\infty=0$.
--   8. AA is equivalent to existence of such bounded Borel approximants with the additional condition
--   $$\lim_k\lim_{\epsilon\downarrow0}\limsup_n\frac1n\sup_x\sup_{y,z\in B_n(x,\epsilon)}|S_nf_k(y)-S_nf_k(z)|=0.$$
--   No expansiveness or specification is imposed. These are separate sufficient conditions and equivalences, with their distinct continuity requirements.
-- source:
--   Fluctuation Theorem and Thermodynamic Formalism, arXiv:1712.05167v3, PDF p. 40, Theorem 6.1: all eight conditions for asymptotic additivity

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P82

noncomputable section

open Filter MeasureTheory Set

open scoped Topology BigOperators ENNReal

namespace QAlgorithms.Papers.Independent.Intake100.P82

attribute [local instance] Classical.propDecidable

section CompactDynamics

variable {M : Type*} [instMetric : MetricSpace M] [instCompact : CompactSpace M]
  [instNonempty : Nonempty M] [instMeasurable : MeasurableSpace M] [instBorel : BorelSpace M]

-- Retain standing assumptions even when a displayed lemma does not use them.

include instCompact instNonempty instBorel

local instance : DecidableEq M := Classical.decEq M

/-- Theorem 6.1, arXiv:1712.05167v3, PDF p.40. All eight assertions,
including their different continuity assumptions and the n/epsilon/k limit order. -/
theorem asymptotic_additivity_characterizations (phi : M → M) (hphi : Continuous phi)
    (G : ℕ → M → ℝ) (hG : BorelSequence G) :
    ((∃ g : C(M, ℝ), ∀ n : ℕ, 1 ≤ n → G n = orbitSum phi g n) →
      AsymptoticallyAdditive phi G) ∧
    ((∃ g : M → ℝ, BoundedBorel g ∧ (∀ n : ℕ, 1 ≤ n → G n = orbitSum phi g n)) →
      TemperedVariation phi G → AsymptoticallyAdditive phi G) ∧
    (WeakAlmostAdditive phi G → (∀ n : ℕ, 1 ≤ n → Continuous (G n)) →
      AsymptoticallyAdditive phi G) ∧
    (WeakAlmostAdditive phi G → TemperedVariation phi G → AsymptoticallyAdditive phi G) ∧
    ((∀ n : ℕ, 1 ≤ n → Continuous (G n)) →
      (AsymptoticallyAdditive phi G ↔ SelfBlockApproximation phi G)) ∧
    (AsymptoticallyAdditive phi G ↔ TemperedVariation phi G ∧ SelfBlockApproximation phi G) ∧
    (AsymptoticallyAdditive phi G ↔ TemperedVariation phi G ∧
      ∃ F : ℕ → M → ℝ, BorelSequence F ∧ AdditiveApproximation phi G F) ∧
    (AsymptoticallyAdditive phi G ↔ ∃ F : ℕ → M → ℝ,
      BorelSequence F ∧ AdditiveApproximation phi G F ∧ ApproximantVariation phi F) := by sorry

end CompactDynamics

end QAlgorithms.Papers.Independent.Intake100.P82

end
