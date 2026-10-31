-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P34_entropy_large_deviations
-- name    : QAlgorithms.Papers.Independent.Intake100.P34.entropy_large_deviations
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T18:05:24.620658+00:00
-- url     : https://prove2.me/theorems/21ed96f2-9cd3-4c20-8e9d-d30ba0bb4d08
-- title:
--   Corollary 3.2 — large deviations, with small-time source correction
-- statement:
--   For the specified detailed-balance QDS with $d>0$, assume positivity improvement at every positive time. Let $e$ be its real spectral cumulant function, $\bar s=-\nabla e(0)$, and
--
--   $$I(s)=\sup_{\alpha\in\mathbb R^M}\{-\alpha\cdot s-e(\alpha)\}.$$
--
--   The extended-real function $I$ is nonnegative, convex and lower semicontinuous, has compact finite sublevel sets, and vanishes exactly at $\bar s$. For each initial state and $\epsilon>0$ there are $a>0$ and $T>0$ such that $P^t_\rho(\|s-\bar s\|_2\ge\epsilon)\le e^{-ta}$ for $t\ge T$. This corrects the printed assertion for all positive times.
--
--   For every Borel set $G$,
--
--   $$-\inf_{G^\circ}I\le\liminf_{t\to\infty}t^{-1}\log P^t_\rho(G)\le\limsup_{t\to\infty}t^{-1}\log P^t_\rho(G)\le-\inf_{\overline G}I.$$
--
--   Here $\log0=-\infty$ and the infimum of the empty set is $+\infty$. Common time reversal implies $I(-s)=\sum_js_j+I(s)$. A common Gibbs Hamiltonian at positive inverse temperatures implies $I(s)=+\infty$ whenever $\beta^{-1}\cdot s\ne0$. These conclusions give the full large-deviation description.
-- source:
--   Entropic fluctuations of quantum dynamical semigroups, arXiv:1305.4409v2, PDF p. 8, Corollary 3.2

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P34

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ENNReal NNReal Matrix.Norms.L2Operator ComplexOrder

open MeasureTheory Filter

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Intake100.P34

open QAlgorithms (IsDensityMatrix)

open QAlgorithms.Papers.Independent.Dependency50.P16 (sandwich)

open QAlgorithms.Papers.Independent.Information100.P26 (Mat commutant scalars)

open QAlgorithms.Papers.Independent.Information100.P30 (MatrixMap IsPositiveMap)

open QAlgorithms.Papers.Independent.Information100.P56 (entropy)

open QAlgorithms.Papers.Independent.Information100.P69 (Faithful)

open QAlgorithms.Papers.Independent.Bridge50.P37 (hsAdjoint)

open QAlgorithms.Papers.Independent.Claimed50.P15
  (evaluate finiteRelativeEntropyNats entropyObservable)

open QAlgorithms.Papers.Independent.Claimed50.P43 (chaotic)

/-- PDF p.3: complex linear superoperators. -/
local notation "GeneratorMap" => fun d : ℕ => MatrixMap (Fin d) (Fin d)

/-- PDF pp.8–9, Corollary 3.2. SOURCE CORRECTION: the printed all-t tail bound is replaced
by an eventual bound; a jump lattice can miss the evaluate's epsilon ball at small times.
All rate and log-probability operations retain extended-real infinities. -/
theorem entropy_large_deviations {d M : ℕ} (D : DBData d M) (hER : ER D) :
    (∀ s : EntropyCoordinates M, 0 ≤ rateFunction D s) ∧ LowerSemicontinuous (rateFunction D) ∧
    (∀ x y : EntropyCoordinates M, ∀ r : ℝ, 0 < r → r < 1 →
      rateFunction D (r • x + (1 - r) • y) ≤
        (r : EReal) * rateFunction D x + ((1 - r : ℝ) : EReal) * rateFunction D y) ∧
    (∀ ell : ℝ, 0 ≤ ell → IsCompact {s : EntropyCoordinates M | rateFunction D s ≤ (ell : EReal)}) ∧
    (∀ s : EntropyCoordinates M, rateFunction D s = 0 ↔ s = entropyMean D) ∧
    (∀ rho, IsDensityMatrix rho → ∀ eps : ℝ, 0 < eps → ∃ a : ℝ, 0 < a ∧
      ∃ T : ℝ, 0 < T ∧ ∀ t ≥ T,
        efcs D rho t {s | eps ≤ length (s - entropyMean D)} ≤ ENNReal.ofReal (Real.exp (-t * a))) ∧
    (∀ rho, IsDensityMatrix rho → ∀ G : Set (EntropyCoordinates M), MeasurableSet G →
      -(⨅ s ∈ interior G, rateFunction D s) ≤ Filter.liminf (scaledLog (efcs D rho) G) atTop ∧
      Filter.liminf (scaledLog (efcs D rho) G) atTop ≤ Filter.limsup (scaledLog (efcs D rho) G) atTop ∧
      Filter.limsup (scaledLog (efcs D rho) G) atTop ≤ -(⨅ s ∈ closure G, rateFunction D s)) ∧
    (TR D → ∀ s : EntropyCoordinates M, rateFunction D (-s) = ((∑ j, s j : ℝ) : EReal) + rateFunction D s) ∧
    (∀ H : Mat d, ∀ beta : EntropyCoordinates M, Thermal D H beta → ∀ s : EntropyCoordinates M,
      reservoirPairing (fun j => (beta j)⁻¹) s ≠ 0 → rateFunction D s = ⊤) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P34

end
