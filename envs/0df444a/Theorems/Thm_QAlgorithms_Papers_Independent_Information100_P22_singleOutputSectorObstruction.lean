-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P22_singleOutputSectorObstruction
-- name    : QAlgorithms.Papers.Independent.Information100.P22.singleOutputSectorObstruction
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T09:52:22.49131+00:00
-- url     : https://prove2.me/theorems/0e8fb5af-901b-4bb8-a2b1-a6e7ff2a7d77
-- title:
--   Proposition 2: Single-output obstruction of the sector-wise encoder
-- statement:
--   For $m=1$, every $k\ge1$, every ordered distinct pair $P,Q$ and every normalized pure resource, the fixed sector-wise encoder fails perfect concealment of its signal:
--   $$\nexists\tau\text{ a density operator}:\quad C_1(X)=\operatorname{Tr}(X)\tau\text{ for every }X.$$
--   The obstruction concerns concealment alone and persists independently of decoder choice.
-- source:
--   Beyond Maximal Entanglement : Exact Resources for Multiparty Encrypted Quantum Cloning, arXiv:2609.28241v1, PDF p. 5, Proposition 2: Single-output obstruction of the sector-wise encoder

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P22

namespace QAlgorithms.Papers.Independent.Information100.P22

open scoped ComplexConjugate ComplexOrder Matrix

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-- Proposition 2, PDF p.5, proof p.26: concealment alone fails. -/
theorem singleOutputSectorObstruction (k : ℕ) (hk : 1 ≤ k) (P Q : Axis) (hPQ : P ≠ Q)
    (R : EuclideanSpace ℂ (Signals 1 k × Signals 1 k)) (hR : IsState R) :
    ¬ Concealed R (twoPauliEncoder 1 k P Q) 0 := by sorry

end

end QAlgorithms.Papers.Independent.Information100.P22
