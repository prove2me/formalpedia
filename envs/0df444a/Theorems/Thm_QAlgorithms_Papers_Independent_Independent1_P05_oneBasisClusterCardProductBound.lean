-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Independent1_P05_oneBasisClusterCardProductBound
-- name    : QAlgorithms.Papers.Independent.Independent1.P05.oneBasisClusterCardProductBound
-- status  : Open
-- author  : @fizzyinc3
-- created : 2026-10-22T17:53:28.245445+00:00
-- url     : https://prove2.me/theorems/42133eaa-7f29-4723-a051-de04f7298729
-- title:
--   Product bound for CSS cluster cardinalities
-- statement:
--   For a binary CSS presentation with positive block length and positive logical dimension, any selected standard-basis cluster and any selected Hadamard-basis cluster satisfy |B_z| |B_x| / 2^n ≤ 1/2 whenever the cluster radius obeys the cutoff in Lemma 2. The estimate isolates the finite Hamming-ball and dual-code counting step used with the conjugate-basis uncertainty bound.
-- source:
--   Anshu, Breuckmann, and Nirkhe, “NLTS Hamiltonians from Good Quantum Codes,” arXiv:2206.13228v4, Lemma 2, proof, PDF p. 4: cluster cardinality estimate and CSS dimension count.

import Definitions.Def_QAlgorithms_Defs_NLTSPreparationCircuits
import Definitions.Def_QAlgorithms_Defs_Measurement
import Definitions.Def_QAlgorithms_Papers_Independent_Independent1_P05_Model
noncomputable section
open scoped Matrix ComplexOrder
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq
namespace QAlgorithms.Papers.Independent.Independent1.P05
open PresentedCSS

theorem oneBasisClusterCardProductBound {n mx mz : ℕ} (C : CheckPresentation n mx mz)
    (hn : 0 < n) (hk : 1 ≤ C.logicalDimension) (c1 eps1 : ℝ)
    (hc1 : 0 < c1) (heps : 0 ≤ eps1)
    (hcutoff : 2*c1*eps1 ≤ (((C.logicalDimension : ℝ)-1)/(4*n))^2)
    (Bz : Finset (NLTSWord n)) (hz : Bz ∈ nltsClasses C c1 eps1 false)
    (Bx : Finset (NLTSWord n)) (hx : Bx ∈ nltsClasses C c1 eps1 true) :
    (Bz.card : ℝ)*Bx.card/(2 : ℝ)^n ≤ 1/2 := by sorry
end QAlgorithms.Papers.Independent.Independent1.P05
