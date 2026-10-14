-- Prove2me | Theorems.Thm_QAlgorithms_GottesmanIntro_output_eq_tilde
-- name    : QAlgorithms.GottesmanIntro.output_eq_tilde
-- status  : Open
-- author  : @Goku
-- created : 2026-10-13T18:05:57.279215+00:00
-- url     : https://prove2.me/theorems/9f02f254-0631-465e-b90a-6cd0dc8faa5b
-- title:
--   A fault-tolerant circuit simulates the ideal circuit with errors at the bad ExRecs
-- statement:
--   Fix an $[[n,1,2t+1]]$ quantum code together with fault-tolerant gadgets for preparation of $|0\rangle$, standard-basis measurement, the gates $H$, $R_{\pi/8}$, CNOT, the wait location, and error correction (Definitions 2–5), all location gadgets having a common depth. Let $C$ be a circuit on $N$ qubits divided into time steps as in Definition 6 (no input, every qubit prepared first and measured last), and let $C'$ be its fault-tolerant circuit, obtained by replacing every location by its gadget and inserting EC gadgets between consecutive locations. Let $W$ be a $*$-decoder for the ideal decoder, i.e. a unitary from a code block to one qubit $\otimes$ a syndrome register $\{0,\dots,\sigma-1\}$ whose syndrome-discarded version is the ideal decoder.
--
--   Let a Pauli fault arrangement be placed on the locations of $C'$, and let $B$ be the set of locations of $C$ whose extended rectangles are bad, assigned from the end of the circuit by the truncation procedure of Definition 10. Then there are an initial state $\sigma_0$ of $N$ syndrome registers (one per qubit of $C$) and a circuit $\tilde C$ obtained from $C$ as follows:
--
--   1. at a location $C_i\notin B$, the ideal operation of $C_i$ on the data, followed by some quantum operation $V_i$ acting only on the syndrome registers of the qubits of $C_i$;
--   2. at a location $C_i\in B$, the ideal operation followed by some quantum operation $U'_i$ on the qubits of $C_i$ together with their syndrome registers,
--
--   such that
--
--   $$\Pr_{C'}[\text{decoded record}=r] = \Pr_{\tilde C}[\text{record}=r]\quad\text{for every measurement record } r \text{ of } C.$$
--
--   The output of $C'$ is decoded classically, block by block, by the decoding of the measurement gadgets. The theorem says that a fault-tolerant circuit behaves like the ideal circuit with errors only at the bad extended rectangles, and is the basis of the level-reduction theorem.
--
--   **Formalization Note** The error $U'$ “from eq. (82)” is whatever makes that diagram hold, so it is quantified existentially; the syndrome registers of $\tilde C$ are the $*$-decoder syndromes, which is why good locations may act on them by the operation $V$ of eq. (83).
-- source:
--   Daniel Gottesman, An Introduction to Quantum Error Correction and Fault-Tolerant Quantum Computation, 2009, v1, PDF p. 39, Theorem 8. https://arxiv.org/pdf/0904.2557v1

import Definitions.Def_QAlgorithms_Defs_FTCircuit
import Definitions.Def_QAlgorithms_GottesmanIntro_Ch05b_Model
set_option autoImplicit false

namespace QAlgorithms.GottesmanIntro




/-- Gottesman intro p.39, Theorem 8: "Suppose we have a fault-tolerant circuit `C′` for `C`.
Assign good and bad extended rectangles to `C′`, and produce a circuit `C̃` as follows: If the
ExRec for `C_i` is good, include `C_i` unchanged in `C̃`. If the ExRec for `C_i` is bad, replace
`C_i` by the erroneous gate `U′` from eq. (82) … The circuit `C̃` uses ancilla registers to
control the types of `U′` errors. Then the output distribution of `C′` is the same as the output
distribution of `C̃`."

Let `P` be a fault-tolerant protocol, `C` a Def. 6 circuit, `fa` a Pauli fault arrangement on
`C′ = ftCircuit P C`, and `W` a *-decoder for the ideal decoder with syndrome register `Fin σ`.
Let `B` be the set of bad locations of `C` assigned by Def. 10 from the faulty locations of `C′`.
Then there are an initial state `σ0` of the syndrome registers (one per qubit of `C`) and errors
forming a circuit `C̃` (`IsTildeErrors`: at a good location, the ideal operation on the data
followed by some operation `V` on the syndrome registers of its qubits only; at a bad location,
the ideal operation followed by an arbitrary quantum operation `U′` on its qubits and their
syndrome registers) such that the decoded output distribution of the faulty `C′` equals the output
distribution of `C̃`. -/
theorem output_eq_tilde (P : FTProtocol) (hP : P.IsFaultTolerant) (hdepth : P.HasUniformDepth)
    {N : ℕ} (C : LocCircuit N) (hC : C.IsIdealCircuit) (fa : PauliArrangement) {σ : ℕ}
    (W : Matrix (Bool × Fin σ) (Qubits P.n) ℂ) (hW : IsStarDecoder P.dec W) :
    ∃ (σ0 : Matrix (Fin N → Fin σ) (Fin N → Fin σ) ℂ) (err : ErrAssign N (Fin N → Fin σ)),
      IsDensityMatrix σ0 ∧
      IsTildeErrors C (badAssignment P C (faultyLocs (ftCircuit P C) fa)) σ err ∧
      pushDist (ftDecode P C) ((ftCircuit P C).outDist (pauliErr (ftCircuit P C) fa) 1) =
        C.outDist err σ0 := by
  sorry



end QAlgorithms.GottesmanIntro
