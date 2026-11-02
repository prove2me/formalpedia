-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P74_phase_encoder_duality
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P74.phase_encoder_duality
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T10:05:52.222347+00:00
-- url     : https://prove2.me/theorems/7ba2565d-682e-47fa-bb8d-4f6d356fd7d9
-- title:
--   Coherent polar encoder and reversed phase side information
-- statement:
--   Let $\mathcal N:A'\to BE$ be a memoryless finite-register quantum wiretap channel with qubit input, with a fixed isometric extension $V:A'\to BES_2$. Choose two unit purifications $|\psi_z\rangle^{A'S_1}$ of the input states, with $z\in\{0,1\}$ equiprobable. Both shields $S_1,S_2$ are excluded from Eve. Let $W_{A,B}$ and $W_{A,E}$ be the resulting amplitude channels to Bob and Eve. The virtual phase channel $W_{P,B}$ has output $BCS_1S_2$, obtained by phase modulating the reference of the coherent source $2^{-1/2}\sum_z|z\rangle^C|\psi_z\rangle$ and tracing only Eve after $V$. Entropies and Holevo information are in bits, and $F$ denotes squared fidelity.
--
--   For $N=2^n$ and a phase input row vector $x^N$, form the coherent output
--
--   $$
--   |\Omega_{x^N}\rangle=2^{-N/2}\sum_{z^N}(-1)^{x^N\cdot z^N}
--    |\psi_{z^N G_N}\rangle^{B^NE^NS_1^NS_2^N}|z^N\rangle^{C^N},
--   $$
--
--   where the signal vector is the product of the one-use purified outputs. Let $\omega_{y^N}=\bigotimes_j\omega_{y_j}$ be the product virtual phase output and let $U_E^{C^N}$ be the polar encoder acting only on the reference register. Then
--
--   $$
--   \operatorname{Tr}_{E^N}|\Omega_{x^N}\rangle\langle\Omega_{x^N}|
--   =U_E^{C^N}\omega_{x^N G_N^T}(U_E^{C^N})^\dagger.
--   $$
--
--   For each index, the split state obtained by revealing future phase bits and averaging earlier phase bits equals the corresponding split of the transposed product phase channel, conjugated by the same reference encoder. This supplies the phase construction used for the polar good-index sets.
-- source:
--   Polar codes for private classical communication, arXiv:1203.5794v1, PDF p. 3, §II.B, unnumbered: coherent polar encoder and reversed phase side information

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P74

namespace QAlgorithms.Papers.Independent.Intakethird100.P74

open QAlgorithms

open scoped ComplexConjugate Matrix

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

variable {B E S1 S2 : Type}

variable [Fintype B] [Fintype E] [Fintype S1] [Fintype S2]

variable [DecidableEq B] [DecidableEq E] [DecidableEq S1] [DecidableEq S2]

/-- PDF pp.3–4, §II.B: row-vector x G_N^T and extra conjugation on C^N.
The second equality spells out the future-bit side information of phase splitting. -/
theorem phase_encoder_duality (d : WiretapData B E S1 S2) (hd : d.Valid) :
    (∀ (n : ℕ) (x : Qubits (2 ^ n)), encodedPhaseOutput d n x =
      referenceEncoder d n * QAlgorithms.Papers.Independent.Information100.P56.productOutput (2 ^ n) (phaseBob d) (polarEncode n true x) *
        (referenceEncoder d n)ᴴ) ∧
    (∀ (n : ℕ) (i : Fin (2 ^ n)) (b : Bool), actualPhaseSplit d n i b =
      idTensorSuperop (conjSuperop (referenceEncoder d n))
        (splitOutput n true (phaseBob d) i b)) := by sorry

end

end QAlgorithms.Papers.Independent.Intakethird100.P74
