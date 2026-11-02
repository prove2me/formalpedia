-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P65_wired_choi_link
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P65.wired_choi_link
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T08:59:55.017798+00:00
-- url     : https://prove2.me/theorems/b8187a73-1539-4abc-ae3d-eafb35255822
-- title:
--   Lemma 13 / Eq.(106): Choi link product for a wired code
-- statement:
--   All systems have finite positive dimension and fixed computational bases. Matrix order is Loewner order and logarithms are base two.
--
--   Let $\mathcal N:A_o\to B_i$ be CPTP and let $\Pi:A_iB_i\to A_oB_o$ be a bipartite CPTP code no-signalling in both directions. Define $\widetilde{\mathcal M}:A_i\to B_o$ by wiring the actual operations through $\mathcal N$, independently of their Choi matrices. Then
--
--   $$J_{\widetilde{\mathcal M}}=\operatorname{Tr}_{A_oB_i}[(J_{\mathcal N}^{T}\otimes I_{A_iB_o})J_\Pi].$$
--
--   The transpose acts on the entire resource Choi matrix, with explicit register permutations. The formula relates the independently wired channel to its Choi representation.
-- source:
--   Quantum Channel Simulation and the Channel's Smooth Max-Information, arXiv:1807.05354v2, PDF p. 21, Lemma 13 / Eq.(106): Choi link product for a wired code

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

/-- Lemma 13, Eq.(106), PDF p.21: link product of independently wired operations.
The entry formula includes the full resource transpose via trace contraction. -/
theorem wired_choi_link (N : Superop B C) (hN : IsChannel N)
    (P : Superop (A × C) (B × D)) (hP : BipartiteNSOperation P) :
    choi (wire N P) = linkChoi (choi N) (choi P) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P65

end
