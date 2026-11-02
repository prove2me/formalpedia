-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P65_ns_reverse_shannon
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P65.ns_reverse_shannon
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T08:48:52.014797+00:00
-- url     : https://prove2.me/theorems/aa605523-303d-40ad-86af-f6d044418c07
-- title:
--   §IV.B: quantum reverse Shannon theorem under NS assistance
-- statement:
--   All systems have finite positive dimension and fixed computational bases. Matrix order is Loewner order and logarithms are base two.
--
--   Let $\mathcal N:A\to B$ be CPTP. Let $Q_{\rm NS}$ be the supremum of operational vanishing-error quantum communication rates with NS assistance, and $S_{\rm NS}$ the infimum of operational vanishing-error simulation rates with the same assistance. These rates count the binary logarithm of noiseless resource dimension per channel use. Then
--
--   $$Q_{\rm NS}(\mathcal N)=S_{\rm NS}(\mathcal N)=\tfrac12 I(\mathcal N).$$
--
--   Here $I(\mathcal N)$ is the maximum state mutual information over purified inputs. This is the quantum reverse Shannon theorem under no-signalling assistance.
-- source:
--   Quantum Channel Simulation and the Channel's Smooth Max-Information, arXiv:1807.05354v2, PDF p. 10, §IV.B: quantum reverse Shannon theorem under NS assistance

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P65

noncomputable section

open Filter QAlgorithms

open scoped BigOperators Matrix ComplexConjugate ComplexOrder Topology

namespace QAlgorithms.Papers.Independent.Intakethird100.P65

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Dependency50.P09 (transposeBob)

open QAlgorithms.Papers.Independent.Dependency50.P35 (maxRelative)

open QAlgorithms.Papers.Independent.Independent2.P01 (dampingKraus damping)

open QAlgorithms.Papers.Independent.Gap48.P33 (phaseFlipChannel)

open QAlgorithms.Papers.Independent.Information100.P06 (Below)

open QAlgorithms.Papers.Independent.Information100.P34 (choi)

open QAlgorithms.Papers.Independent.Information100.P62 (Stochastic)

open QAlgorithms.Papers.Independent.Information100.P63 (Mat)

open QAlgorithms.Papers.Independent.Information100.P67 (IsSubnormalized purifiedDistance)

open QAlgorithms.Papers.Independent.Information100.P69 (replacer permute)

open QAlgorithms.Papers.Independent.Information100.P71 (diamond channelPower channelRelative)

open QAlgorithms.Papers.Independent.Support50.P39 (quantumMutualInformation)

variable {A B C D R : Type} [Fintype A] [DecidableEq A]
  [Fintype B] [DecidableEq B] [Fintype C] [DecidableEq C]
  [Fintype D] [DecidableEq D] [Fintype R] [DecidableEq R]

variable [Nonempty A] [Nonempty B] [Nonempty C] [Nonempty D] [Nonempty R]

/-- Section IV.B, PDF pp.10--12: quantum reverse Shannon theorem with NS
assistance. Capacity and simulation cost were defined independently of entropy. -/
theorem ns_reverse_shannon (N : Superop A B) (hN : IsChannel N) :
    vanishingErrorQuantumCapacity .ns N = vanishingErrorSimulationCost .ns N ∧
    vanishingErrorSimulationCost .ns N = ((channelMutualInfo N / 2 : ℝ) : EReal) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P65

end
