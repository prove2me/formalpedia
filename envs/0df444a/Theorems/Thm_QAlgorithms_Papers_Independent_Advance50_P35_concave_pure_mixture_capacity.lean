-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P35_concave_pure_mixture_capacity
-- name    : QAlgorithms.Papers.Independent.Advance50.P35.concave_pure_mixture_capacity
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T13:41:11.661726+00:00
-- url     : https://prove2.me/theorems/f3cf56bf-fd71-48c8-b2df-859a56e9efb3
-- title:
--   Concavity equates pure-class and arbitrary-mixture capacities
-- statement:
--   Let $\Phi$ be a finite nonempty ensemble of pairwise distinct single-mode bosonic CPTP channels with fixed normalized priors. Inputs are normalized trace-class states on the full number space; identical transmitters are repeated across different cells, references bypass the channels, and block detection may be collective. All information is in bits, and the exact constraint counts the sum of signal energies only. Let $P$ be an energy-independent class of normalized pure transmitters on each fixed signal/reference register. Let $A$ consist of arbitrary Borel probability mixtures of members of $P$ on those same registers. Define $C_P$ and $C_A$ by optimizing the conditional Holevo information over their respective classes and all finite mode counts at exact mean signal energy $n$. Assume the pure class is feasible at every $n\geq0$. If $n\mapsto C_P(\Phi\mid n)$ is concave on $[0,\infty)$, then
--
--   $$C_P(\Phi\mid n)=C_A(\Phi\mid n)\qquad(n\geq0).$$
--
--   Only the mixture average has energy $n$; components may have different energies $n_y$, with $\int n_y\,dp_y=n$. The result is a criterion for a specified class, not an assertion that all optimal energy-constrained transmitters are pure.
-- source:
--   Quantum Reading Capacity, arXiv:1107.3500v1, PDF p. 9, Lemma 1: concavity makes pure-class and mixture-class capacities equal

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P35

noncomputable section

open MeasureTheory Filter

open scoped BigOperators ENNReal NNReal Topology

namespace QAlgorithms.Papers.Independent.Advance50.P35

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33
  (State PureState IsDensity IsBarycenter tensorApply traceSize)

open QAlgorithms.Papers.Independent.Frontier18.P01 (Channel)

open QAlgorithms.Papers.Independent.Frontier18.P07
  (extendedRelativeEntropyNats binaryEntropyBits)

open QAlgorithms.Papers.Independent.Dependency50.P39 (displacementMatrix coherentCoefficient)

open QAlgorithms.Papers.Independent.Support50.P20 (IsBinaryEffect)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Lemma 1, PDF pp.9--10, using the variable component energies in (56).
Concavity does not assert purity of every unconstrained or constrained optimizer. -/
theorem concave_pure_mixture_capacity {k : ℕ} (M : Memory ℕ k) (P : PureClass)
    (hfeasible : EnergyFeasible P)
    (hconcave : ConcaveOn ℝ (Set.Ici 0) (fun n => (pureClassCapacity M P n).toReal)) :
    ∀ n : ℝ, 0 ≤ n → pureClassCapacity M P n = mixtureClassCapacity M P n := by sorry

end QAlgorithms.Papers.Independent.Advance50.P35

end
