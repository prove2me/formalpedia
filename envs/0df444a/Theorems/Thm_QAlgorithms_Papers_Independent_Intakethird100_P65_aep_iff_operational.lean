-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P65_aep_iff_operational
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P65.aep_iff_operational
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T08:50:31.700523+00:00
-- url     : https://prove2.me/theorems/0b07bf85-d53c-4cf9-94bb-1c910688a26c
-- title:
--   Eq.(44): equivalence of AEP and operational cost identity
-- statement:
--   All systems have finite positive dimension and fixed computational bases. Matrix order is Loewner order and logarithms are base two.
--
--   For a CPTP channel $\mathcal N$, the channel AEP and the equality of entanglement-assisted capacity with NS simulation cost are equivalent:
--
--   $$\left[\lim_{\varepsilon\downarrow0}\lim_{n\to\infty}n^{-1}I_{\max}^{\varepsilon}(\mathcal N^{\otimes n})=I(\mathcal N)\right]\quad\Longleftrightarrow\quad Q_E(\mathcal N)=S_{\rm NS}(\mathcal N).$$
--
--   The limit assertion includes existence in the printed order. Both operational quantities are defined from actual codes; the cited background capacity formula is not made a hypothesis.
-- source:
--   Quantum Channel Simulation and the Channel's Smooth Max-Information, arXiv:1807.05354v2, PDF p. 10, Eq.(44): equivalence of AEP and operational cost identity

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

/-- Eq.(44), PDF p.10: two-way equivalence, without assuming the cited
entanglement-assisted vanishingErrorQuantumCapacity identity as a new hypothesis. -/
theorem aep_iff_operational (N : Superop A B) (hN : IsChannel N) :
    IteratedLimit (fun e n => smoothChannelInfo (channelPower N n) e / n) (channelMutualInfo N) ↔
      vanishingErrorQuantumCapacity .ent N = vanishingErrorSimulationCost .ns N := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P65

end
