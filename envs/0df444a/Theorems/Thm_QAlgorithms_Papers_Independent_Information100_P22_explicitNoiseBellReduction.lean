-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P22_explicitNoiseBellReduction
-- name    : QAlgorithms.Papers.Independent.Information100.P22.explicitNoiseBellReduction
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T09:58:58.686903+00:00
-- url     : https://prove2.me/theorems/580dd2e1-947a-4323-b9db-d985742622c4
-- title:
--   Observation 1: Explicit noise-side Bell reduction
-- statement:
--   Let $\nu\ge1$ and let a standard graph state have ordered cut blocks $A_S,B,A_N$, with $B$ invertible over $\mathbb F_2$. Let $L_M|x\rangle=|Mx\rangle$ and $CZ_A$ be the quadratic graph phase. Then the noise-only Clifford
--   $$U_N=CZ_{A_S}L_{B^{-T}}H^{\otimes\nu}CZ_{A_N}$$
--   satisfies $(I_S\otimes U_N)|G\rangle=|\Phi_{2^\nu}\rangle$, with positive normalized Bell amplitudes $2^{-\nu/2}$. The rightmost factor acts first. No output/input factorization or signal-side operation is required.
-- source:
--   Beyond Maximal Entanglement : Exact Resources for Multiparty Encrypted Quantum Cloning, arXiv:2609.28241v1, PDF p. 11, Observation 1: Explicit noise-side Bell reduction

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P22

namespace QAlgorithms.Papers.Independent.Information100.P22

open scoped ComplexConjugate ComplexOrder Matrix

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

local instance {I : Type*} [Fintype I] [DecidableEq I] (G : CutGraph I) :
    Fintype (cutKernel G) := Fintype.ofFinite _

/-- Observation 1, PDF p.11, proof pp.35–36: no operation on S. -/
theorem explicitNoiseBellReduction (nu : ℕ) (hnu : 1 ≤ nu) (G : CutGraph (Fin nu))
    (hB : IsUnit G.B.det) :
    RegisterClifford (bellNormalizer G) ∧
    act (Matrix.kronecker (1 : Op (Qubits nu)) (bellNormalizer G)) (graphVector G) =
      bell (Qubits nu) := by sorry

end

end QAlgorithms.Papers.Independent.Information100.P22
