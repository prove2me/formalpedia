-- Prove2me | Theorems.Thm_QAlgorithms_GottesmanIntro_steaneEC_claim1
-- name    : QAlgorithms.GottesmanIntro.steaneEC_claim1
-- status  : Open
-- author  : @Goku
-- created : 2026-10-13T17:59:39.975819+00:00
-- url     : https://prove2.me/theorems/380ecdea-610a-41ff-80f4-6b7edaea3e28
-- title:
--   Steane error correction: final errors lie only on the fault locations
-- statement:
--   This is the key claim in the proof that Steane error correction satisfies property EC A (Gottesman intro p.28).
--
--   Let $C_1, C_2 \subseteq \mathbb F_2^n$ be binary linear codes with $C_2^{\perp} \subseteq C_1$, and let $\mathcal C$ be their CSS code, spanned by the states $\sum_{w \in C_2^{\perp}} |u + w\rangle$ for $u \in C_1$. Steane error correction is applied to a data block in an arbitrary state $|\psi\rangle$. The state may be entangled with a reference system $R$, and its incoming error is unrestricted. The procedure runs as follows:
--
--   1. A phase ancilla is prepared in the encoded $|0\rangle = \sum_{w\in C_2^\perp}|w\rangle$ and a bit-flip ancilla in the encoded $|0\rangle+|1\rangle = \sum_{u\in C_1}|u\rangle$.
--   2. A transversal CNOT is applied with the phase ancilla as control and the data as target. Then a transversal CNOT is applied with the data as control and the bit-flip ancilla as target.
--   3. The phase ancilla is measured in the Hadamard-rotated basis, giving a word $w_P$. The bit-flip ancilla is measured in the standard basis, giving $w_B$.
--   4. Classical decoders return $d_P = \mathrm{dec}_P(w_P)$ with the same $C_2$-syndrome as $w_P$ and $d_B = \mathrm{dec}_B(w_B)$ with the same $C_1$-syndrome as $w_B$. Then $Z$ is applied on the qubits of $d_P$ and $X$ on the qubits of $d_B$. This correction step is error-free.
--
--   The faults are arbitrary operators. They may act within $f_P, f_B$ on the prepared ancillas, and within the pairs (data qubit $i$, ancilla qubit $i$) for $i \in g_P$, resp. $g_B$, right after the two CNOTs. During the Hadamard and measurement of the phase ancilla they act within $h_P$, and during the measurement of the bit-flip ancilla within $h_B$. Put $F = f_P \cup f_B \cup g_P \cup g_B \cup h_P \cup h_B$. Then for every pair of outcomes $(w_P, w_B)$ the corrected (unnormalized) data–reference state satisfies
--
--   $$
--   |\psi_{\mathrm{final}}\rangle \in V_F \otimes R, \qquad V_F = \operatorname{span}\{E|c\rangle : c \in \mathcal C,\ E \text{ acts only on the qubits in } F\},
--   $$
--
--   and moreover $|F| \le s = |f_P|+|f_B|+|g_P|+|g_B|+|h_P|+|h_B|$.
--
--   In words: after Steane error correction, the data is a codeword (possibly a different logical state) with errors only on the qubits where faults occurred during error correction. This gives EC A when $s \le t$.
--
--   **Formalization Note** The circuit is the chunk-local definition `steaneECOutput`. It returns the post-measurement branch for the given outcomes, i.e. the amplitude of the ancillas on $|w_P, w_B\rangle$. In that branch the map is linear, so the arbitrary fault operators per Kraus branch and the arbitrary incoming vector cover the source's 'no restrictions as to the types of errors'. The hypothesis $s \le t$ of EC A is omitted because the claim's proof never uses it.
-- source:
--   Daniel Gottesman, An Introduction to Quantum Error Correction and Fault-Tolerant Quantum Computation, 2009, v1, PDF p. 28, §4.4, Claim 1. https://arxiv.org/pdf/0904.2557v1

import Definitions.Def_QAlgorithms_Defs_BinaryStabilizer
import Definitions.Def_QAlgorithms_GottesmanIntro_Ch04_Model
set_option autoImplicit false

namespace QAlgorithms.GottesmanIntro






/-- Gottesman intro p.28, Claim 1 (Steane error correction, proof of EC A): let `C1, C2 ⊆ F_2^n`
be binary linear codes with `C2⊥ ⊆ C1` and let `C` be their CSS code (p.11). Run Steane error
correction (p.27, Figure 3) on an arbitrary incoming data vector `ψ`, possibly entangled with a
reference system `R`, with classical decoders returning an error with the same syndrome as the
measured word (`decP` for `C2`, `decB` for `C1`, p.28). Let the faults be arbitrary operators:
`FP`, `FB` on the prepared phase and bit-flip ancillas, acting within the qubit sets `fP`, `fB`;
`GP`, `GB` at the transversal CNOTs, acting within qubit `i` of the data block and of the
ancilla for `i ∈ gP`, resp. `gB`; `HP`, `HB` during the Hadamard and measurement of the phase
ancilla and the measurement of the bit-flip ancilla, within `hP`, `hB`. Then for every pair of
measurement outcomes the corrected data ⊗ reference state lies in `V_F ⊗ R`, where
`F = fP ∪ fB ∪ gP ∪ gB ∪ hP ∪ hB` and `V_F` is the span of the vectors `E|c⟩` with `c ∈ C` and
`E` acting within `F`: the final state has errors only on the qubits of `F`; and `|F| ≤ s`,
`s = |fP| + |fB| + |gP| + |gB| + |hP| + |hB|`. -/
theorem steaneEC_claim1 {n : ℕ} {R : Type*} [Fintype R] [DecidableEq R]
    (C1 C2 : Submodule (ZMod 2) (Fin n → ZMod 2)) (hC : binDual C2 ≤ C1)
    (decP decB : (Fin n → ZMod 2) → (Fin n → ZMod 2))
    (hdecP : ∀ w : Fin n → ZMod 2, ∀ h ∈ binDual C2, h ⬝ᵥ decP w = h ⬝ᵥ w)
    (hdecB : ∀ w : Fin n → ZMod 2, ∀ h ∈ binDual C1, h ⬝ᵥ decB w = h ⬝ᵥ w)
    (fP fB gP gB hP hB : Finset (Fin n))
    (FP FB HP HB : Matrix (Qubits n) (Qubits n) ℂ)
    (GP GB : Matrix (Qubits n × Qubits n) (Qubits n × Qubits n) ℂ)
    (hFP : ActsWithin fP FP) (hFB : ActsWithin fB FB)
    (hGP : ActsWithinPair gP GP) (hGB : ActsWithinPair gB GB)
    (hHP : ActsWithin hP HP) (hHB : ActsWithin hB HB)
    (ψ : EuclideanSpace ℂ (Qubits n × R)) (wP wB : Fin n → ZMod 2) :
    steaneECOutput C1 C2 decP decB FP FB HP HB GP GB ψ wP wB ∈
        errorSpaceWithRef R (cssCode C1 C2) (fP ∪ fB ∪ gP ∪ gB ∪ hP ∪ hB) ∧
      (fP ∪ fB ∪ gP ∪ gB ∪ hP ∪ hB).card ≤
        fP.card + fB.card + gP.card + gB.card + hP.card + hB.card := by
  sorry

end QAlgorithms.GottesmanIntro
