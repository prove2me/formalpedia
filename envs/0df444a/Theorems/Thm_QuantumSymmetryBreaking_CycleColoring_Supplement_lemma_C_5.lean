-- Prove2me | Theorems.Thm_QuantumSymmetryBreaking_CycleColoring_Supplement_lemma_C_5
-- name    : QuantumSymmetryBreaking.CycleColoring.Supplement.lemma_C_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T21:09:11.066191+00:00
-- url     : https://prove2.me/theorems/b6f948a7-a208-4a3a-aa78-c4ff75e38aee
-- title:
--   Lemma C.5 — Message-dimension-preserving collision-energy representation
-- statement:
--   Consider any anonymous one-way one-round q-color algorithm on a directed n-cycle, with q≥1 and n≥3. Each node prepares an arbitrary mixed density matrix on a private register of any positive finite dimension D and a message register of dimension N=2^k, sends that message to its successor, and measures an arbitrary q-outcome POVM on its received message and private register. There exist a q-outcome POVM (P_a) on ℂ^N⊗ℂ^N and a positive semidefinite matrix Λ on ℂ^N with squared Frobenius norm one such that, for every edge i,
--
--   $$\Pr[c_i=c_{i+1}]=\sum_{a=1}^{q}\mathcal E_\Lambda(P_a),\qquad N=2^k.$$
--
--   The left-hand side is the published full Born-law collision probability. The right-hand side uses the published general weighted energy. The private space is unrestricted and is not assumed to equal the message space. This dimension-preserving representation supports the qubit lower bound.
--
--   Differences from the source:
--   - encoding: general finite private space and k-qubit message → Fin D × Fin (2 ^ k), D > 0, arbitrary mixed state and POVM; reason: purification and any private measurement records fit the unrestricted private space; only the transmitted register is fixed
--   - encoding: directed n-cycle and q colors → n ≥ 3 with NeZero n, q > 0, ZMod n and Fin q; reason: makes the nondegenerate source cycle and palette conventions explicit
--   - encoding: Definition C.4 weighted energy → published energy Λ at a general PSD Λ; reason: the row-first vectorization and spectral formula match the published lemma_4_2 interface
-- source:
--   Maxime Flin, Longcheng Li, Jukka Suomela, Quantum Advantage for Distributed Symmetry Breaking, STOC 2027 submission #863 (October 2026), Lemma C.5, p.47 (PDF 50)

import Mathlib
import Definitions.Def_QuantumCycleColoring_FourColor_CycleAlgorithm
import Definitions.Def_QuantumSymmetryBreaking_CycleColoring_FiniteRealization

set_option autoImplicit false
open scoped ComplexOrder

namespace QuantumSymmetryBreaking.CycleColoring.Supplement

open QuantumCycleColoring.FourColor

/-- Lemma C.5, printed pp.47–48 (PDF 50–51). The private register has
arbitrary positive finite size D; only the transmitted register has dimension 2^k.
Mixed input density matrices and all POVMs are admitted. -/
theorem lemma_C_5 (q k D n : ℕ) [NeZero n] (hq : 0 < q) (hD : 0 < D) (hn : 3 ≤ n)
    (ρ : Matrix (Fin D × Fin (2 ^ k)) (Fin D × Fin (2 ^ k)) ℂ)
    (hρ : IsDensityMatrix ρ)
    (Q : Fin q → Matrix (Fin (2 ^ k) × Fin D) (Fin (2 ^ k) × Fin D) ℂ)
    (hQ : IsPOVM Q) :
    ∃ P : Fin q → Matrix (Fin (2 ^ k) × Fin (2 ^ k)) (Fin (2 ^ k) × Fin (2 ^ k)) ℂ,
    ∃ Λ : Matrix (Fin (2 ^ k)) (Fin (2 ^ k)) ℂ,
      IsPOVM P ∧ Λ.PosSemidef ∧ frobNorm Λ ^ 2 = 1 ∧
      ∀ i : ZMod n, collisionProb n ρ Q i = ∑ a, energy Λ (P a) := by sorry

end QuantumSymmetryBreaking.CycleColoring.Supplement
