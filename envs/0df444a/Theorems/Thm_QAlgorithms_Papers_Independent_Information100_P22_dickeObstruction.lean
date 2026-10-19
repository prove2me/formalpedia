-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P22_dickeObstruction
-- name    : QAlgorithms.Papers.Independent.Information100.P22.dickeObstruction
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T10:00:57.291039+00:00
-- url     : https://prove2.me/theorems/30483dca-2d5d-42b0-a534-a73b9ceab0b1
-- title:
--   Observation 4: Dicke-state obstruction
-- statement:
--   For all $m\ge2$, $k\ge1$, every excitation number $0\le r\le2mk$, and every ordered distinct pair of Pauli axes, the normalized Dicke resource on $2mk$ qubits satisfies
--   $$\rho_S(D_{2mk}^{(r)})\text{ fails Eq.(3)},\qquad\text{all-output exact recovery is impossible}.$$
--   Permutation symmetry includes every balanced cut and sector assignment. This structural obstruction includes the two product endpoints and all encoder frames.
-- source:
--   Beyond Maximal Entanglement : Exact Resources for Multiparty Encrypted Quantum Cloning, arXiv:2609.28241v1, PDF p. 14, Observation 4: Dicke-state obstruction

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P22

namespace QAlgorithms.Papers.Independent.Information100.P22

open scoped ComplexConjugate ComplexOrder Matrix

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

local instance {I : Type*} [Fintype I] [DecidableEq I] (G : CutGraph I) :
    Fintype (cutKernel G) := Fintype.ofFinite _

/-- Observation 4, PDF pp.14,43: every excitation number and every ordered encoder frame. -/
theorem dickeObstruction (m k r : ℕ) (hm : 2 ≤ m) (hk : 1 ≤ k) (hr : r ≤ 2*(m*k))
    (P Q : Axis) (hPQ : P ≠ Q) :
    ¬ ResourceCriterion P Q (rhoS (dickeResource (Wires m k) r)) ∧
    ¬ AllRecoverable (dickeResource (Wires m k) r) (twoPauliEncoder m k P Q) := by sorry

end

end QAlgorithms.Papers.Independent.Information100.P22
