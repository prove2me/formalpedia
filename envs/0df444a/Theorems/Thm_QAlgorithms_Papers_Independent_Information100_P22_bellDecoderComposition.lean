-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P22_bellDecoderComposition
-- name    : QAlgorithms.Papers.Independent.Information100.P22.bellDecoderComposition
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T10:11:01.297287+00:00
-- url     : https://prove2.me/theorems/ff4050f2-392a-4530-b789-207f7945120e
-- title:
--   Eq.(S50), unnumbered: authorized decoder composition
-- statement:
--   For a full-rank graph cut with $m\ge2$, $k\ge1$, fixed encoder and output $i$, there exists an exact CPTP decoder $D_i^{\rm Bell}$ for the canonical Bell resource. The composite
--   $$D_i=D_i^{\rm Bell}\circ\operatorname{Ad}_{I_{S_i}\otimes U_N}$$
--   is CPTP and exactly reverses the graph resource's authorized channel. Here $U_N$ is the specified noise-only normalizer and $\operatorname{Ad}_V(X)=VXV^\dagger$. Both decoder equalities hold on every operator. This keeps canonicalization distinct from full recovery.
-- source:
--   Beyond Maximal Entanglement : Exact Resources for Multiparty Encrypted Quantum Cloning, arXiv:2609.28241v1, PDF p. 11, Eq.(S50), unnumbered: authorized decoder composition

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P22

namespace QAlgorithms.Papers.Independent.Information100.P22

open scoped ComplexConjugate ComplexOrder Matrix

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

local instance {I : Type*} [Fintype I] [DecidableEq I] (G : CutGraph I) :
    Fintype (cutKernel G) := Fintype.ofFinite _

/-- Eq.(S50), PDF pp.11,36: compose the key normalizer with any fixed Bell decoder. -/
theorem bellDecoderComposition (m k : ℕ) (hm : 2 ≤ m) (hk : 1 ≤ k)
    (P Q : Axis) (hPQ : P ≠ Q) (G : CutGraph (Wires m k)) (hB : IsUnit G.B.det) (i : Fin m) :
    ∃ D : Superop (Qubits k × Signals m k) (Qubits k), IsChannel D ∧
      (∀ X, D (authorized (bell (Signals m k)) (twoPauliEncoder m k P Q) i X) = X) ∧
      IsChannel (D ∘ conjSuperop (Matrix.kronecker (1 : Op (Qubits k)) (bellNormalizer G))) ∧
      ∀ X, D (conjSuperop (Matrix.kronecker (1 : Op (Qubits k)) (bellNormalizer G))
        (authorized (graphVector G) (twoPauliEncoder m k P Q) i X)) = X := by sorry

end

end QAlgorithms.Papers.Independent.Information100.P22
