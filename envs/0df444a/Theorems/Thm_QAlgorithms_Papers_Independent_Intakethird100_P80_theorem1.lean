-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P80_theorem1
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P80.theorem1
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T09:22:31.985222+00:00
-- url     : https://prove2.me/theorems/a163b35d-3a9c-4160-8955-775668ed5412
-- title:
--   All analytic and optimizer properties of statistical strength
-- statement:
--   Fix a finite quantum-generated, normalized, no-signalling conditional table $Q$. Write $\Sigma$ for the setting simplex and $\Pi$ for the simplex on all complete potential-outcome assignments $v$. For $\pi\in\Pi$, let $P_{s;\pi}$ be its measured marginal, $U(\sigma,\pi)=D_2(Q_\sigma\|P_{\sigma;\pi})$, and $u(\sigma)=\inf_{\pi\in\Pi}U(\sigma,\pi)$.
--
--   1. For every setting law, the joint divergence is the average conditional divergence:
--   $$U(\sigma,\pi)=\sum_s\sigma_sD_2(Q_s\|P_{s;\pi}).$$
--   For fixed $\sigma$, $U$ is convex and lower semicontinuous on $\Pi$, and finite, continuous, and differentiable at its relative interior. For fixed $\pi$ supporting $Q$ at every setting, $U$ is linear in $\sigma$.
--   2. Every infimum defining $u$ is attained. The function $u$ is finite, nonnegative, bounded uniformly over $\Sigma$, concave, and continuous on the entire simplex. If $Q$ has a local model, $u$ vanishes everywhere. Otherwise $u(\sigma)>0$ at every full-support setting law. For two parties with two settings each, $u$ vanishes at every boundary setting law, with arbitrary nonempty finite outcome alphabets.
--   3. Suppose $\sigma_s>0$ for every $s$. If some conditional probability of $Q$ lies strictly between zero and one, a local law $\pi$ minimizes $U(\sigma,\cdot)$ if and only if it supports $Q$ and, writing $v_s$ for the outcomes selected from $v$,
--   $$g_\pi(v)=\sum_s\sigma_s\frac{Q_s(v_s)}{P_{s;\pi}(v_s)}=1\ \ (\pi_v>0),\qquad g_\pi(v)\le1\ \ (\pi_v=0).$$
--   A zero numerator contributes zero. Any two minimizers have identical, strictly positive measured probabilities on every positive-$Q$ outcome, and both support $Q$ at every setting.
--
--   These conclusions give the optimization and first-order characterization for a fixed experiment. Relative interior means positive simplex coordinates; differentiability is taken within the simplex. The explicit support guard prevents real division by zero from discarding the singular cases.
-- source:
--   The statistical strength of nonlocality proofs, arXiv:quant-ph/0307125v2, PDF p. 12, Theorem 1: all basic analytic and optimizer properties

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P80

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P80

open scoped BigOperators ENNReal Topology Classical

open MeasureTheory Filter

/-- PDF p.12, Theorem 1, all parts; proof pp.32–34. Relative full support is used.
The ratio test includes the support condition implicit in the differentiation argument on p.34.
Uniqueness is asserted only on positive-Q events, correcting the later prose overstatement. -/
theorem theorem1 {S : BellExperiment} (Q : Table S) (hQ : NonlocalityProof Q) :
    (∀ s : Sigma S, ∀ p : PiLocal S,
      statisticalPayoff Q s.1 p.1 = ∑ a, ENNReal.ofReal (s.1 a) * kl (Q a) (localTable p.1 a)) ∧
    (∀ s : Sigma S,
      (∀ (p r : PiLocal S) (a b : ℝ), 0 ≤ a → 0 ≤ b → a + b = 1 →
        statisticalPayoff Q s.1 (a • p.1 + b • r.1) ≤
          ENNReal.ofReal a * statisticalPayoff Q s.1 p.1 + ENNReal.ofReal b * statisticalPayoff Q s.1 r.1) ∧
      LowerSemicontinuousOn (fun p => statisticalPayoff Q s.1 p) (stdSimplex ℝ (Potential S)) ∧
      (∀ p : PiLocal S, PositiveCoordinates p.1 →
        statisticalPayoff Q s.1 p.1 < ⊤ ∧
        ContinuousWithinAt (fun r => statisticalPayoff Q s.1 r) (stdSimplex ℝ (Potential S)) p.1 ∧
        DifferentiableWithinAt ℝ (fun r => (statisticalPayoff Q s.1 r).toReal)
          (stdSimplex ℝ (Potential S)) p.1)) ∧
    (∀ p : PiLocal S, DominatesQuantum Q p.1 →
      ∃ L : (Settings S → ℝ) →ₗ[ℝ] ℝ,
        ∀ s : Sigma S, statisticalPayoff Q s.1 p.1 = ENNReal.ofReal (L s.1)) ∧
    (∀ s : Sigma S, ∃ p : PiLocal S, statisticalPayoff Q s.1 p.1 = lowerValue Q s.1) ∧
    ((∀ s : Sigma S, 0 ≤ lowerValue Q s.1 ∧ lowerValue Q s.1 < ⊤) ∧
      (∃ B : ℝ≥0∞, B < ⊤ ∧ ∀ s : Sigma S, lowerValue Q s.1 ≤ B) ∧
      ConcaveOn ℝ (stdSimplex ℝ (Settings S)) (fun s => (lowerValue Q s).toReal) ∧
      ContinuousOn (fun s => (lowerValue Q s).toReal) (stdSimplex ℝ (Settings S))) ∧
    ((¬ Proper Q → ∀ s : Sigma S, lowerValue Q s.1 = 0) ∧
      (Proper Q → ∀ s : Sigma S, PositiveCoordinates s.1 → 0 < lowerValue Q s.1)) ∧
    (TwoByTwo S → ∀ s : Sigma S, (∃ a, s.1 a = 0) → lowerValue Q s.1 = 0) ∧
    (∀ s : Sigma S, PositiveCoordinates s.1 →
      (NontrivialTable Q → ∀ p : PiLocal S,
        (statisticalPayoff Q s.1 p.1 = lowerValue Q s.1 ↔
          DominatesQuantum Q p.1 ∧
          (∀ v, 0 < p.1 v → optimizerScore Q s.1 p.1 v = 1) ∧
          (∀ v, p.1 v = 0 → optimizerScore Q s.1 p.1 v ≤ 1))) ∧
      (∀ p r : PiLocal S,
        statisticalPayoff Q s.1 p.1 = lowerValue Q s.1 →
        statisticalPayoff Q s.1 r.1 = lowerValue Q s.1 →
        DominatesQuantum Q p.1 ∧ DominatesQuantum Q r.1 ∧
        ∀ a x, 0 < Q a x → localTable p.1 a x = localTable r.1 a x ∧
          0 < localTable p.1 a x)) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P80

end
