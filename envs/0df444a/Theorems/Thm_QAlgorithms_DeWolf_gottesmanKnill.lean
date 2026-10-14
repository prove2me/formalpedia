-- Prove2me | Theorems.Thm_QAlgorithms_DeWolf_gottesmanKnill
-- name    : QAlgorithms.DeWolf.gottesmanKnill
-- status  : Open
-- author  : @Goku
-- created : 2026-10-13T17:43:31.828678+00:00
-- url     : https://prove2.me/theorems/e261f9b1-265f-46a4-a7d7-708b470686b4
-- title:
--   Gottesman–Knill: measurement-controlled Clifford circuits are efficiently classically simulable
-- statement:
--   This is the Gottesman–Knill theorem.
--
--   Let $\mathcal P_n=\{\pm1,\pm i\}\cdot\{I,X,Y,Z\}^{\otimes n}$ be the $n$-qubit Pauli group. A *measurement-controlled Clifford circuit family* $F=\{C_n\}$ consists, for each number of qubits $n$, of a sequence of at most $s(n)$ operations, $s$ a polynomial, each of which is a Pauli gate, a Hadamard gate $H$, the phase gate $S=\mathrm{diag}(1,i)$, a CNOT gate, or the projective measurement of a Pauli $M\in\{I,X,Y,Z\}^{\otimes n}$ with projectors $M_\pm=(I\pm M)/2$. The next operation is computed from $n$, a string $r$ of $q(n)$ uniformly random bits ($q$ a polynomial) and the outcomes of the earlier measurements by a classical polynomial-time algorithm. Running $C_n$ on the computational basis state $|x\rangle$, $x\in\{0,1\}^n$, produces a random final pure state $|\psi\rangle$; write $\mathcal D_F(n,x)$ for the distribution of its density matrix $|\psi\rangle\langle\psi|$.
--
--   A *stabilizer description* (tableau) is a list $P^{(1)},\dots,P^{(n)}\in\mathcal P_n$ with phases $\pm1$ that pairwise commute, are independent (none is a phase times a product of the others) and do not generate $-I$; it describes the state with density matrix $\prod_{j=1}^n \tfrac12(I+P^{(j)})$.
--
--   **Theorem.** For every measurement-controlled Clifford circuit family $F$ there is a randomized classical polynomial-time algorithm $A$ such that for every $n$ and every $x\in\{0,1\}^n$:
--
--   1. every possible output of $A$ on input $(n,x)$ is the encoding of a stabilizer description $T=(P^{(1)},\dots,P^{(n)})$;
--   2. the distribution of the described state satisfies
--   $$\Pr_{A}\Big[\textstyle\prod_{j=1}^n \tfrac12\big(I+P^{(j)}\big)=\rho\Big]=\Pr_{\mathcal D_F(n,x)}\big[|\psi\rangle\langle\psi|=\rho\big]\quad\text{for every matrix }\rho .$$
--
--   Thus Clifford circuits with intermediate Pauli measurements and classical (randomized) control, started on a basis state, can be sampled exactly by a classical computer; the quantum advantage requires non-Clifford resources such as the $T$ gate.
--
--   **Formalization Note** The source says the simulator is "given C"; following its own remark on p.187 that one strictly has to speak of families $\{C_n\}$, the simulator is fixed for the family (chosen before $n$ and $x$) and receives $(n,x)$ encoded as a bit string. Polynomial time is the Turing-machine notion `PolyTimeComputable` of this repository, applied to the input followed by a uniformly random string of polynomial length. Distributions over states are compared via density matrices, so the global phase is ignored, as in the source's footnote 3 on p.185.
-- source:
--   Ronald de Wolf, Quantum Computing: Lecture Notes, 27 August 2026, PDF p. 187, §20.3, Theorem 6. https://homepages.cwi.nl/~rdewolf/qcnotes.pdf

import Definitions.Def_QAlgorithms_Defs_Stabilizer
set_option autoImplicit false

namespace QAlgorithms.DeWolf

open QAlgorithms.Stabilizer QAlgorithms.Complexity

/-- **Theorem 6 (Gottesman–Knill)**, de Wolf §20.3, PDF p.187 (proof pp.187–188).

"There exists a classical polynomial-time algorithm that, given an n-qubit
measurement-controlled Clifford circuit C and an n-qubit initial basis state |x⟩, samples from
the same final probability distribution over stabilizer states as C. The classical simulator
will output a stabilizer description of the sampled final state."

Following the source's own remark on p.187 ("strictly speaking we'd have to talk about families
of circuits {Cₙ}"), the circuit is a family `F` of measurement-controlled Clifford circuits
(Pauli, H, S, CNOT gates and Pauli measurements `M ∈ {I,X,Y,Z}^{⊗n}`, the next operation computed
from the random bits and the earlier outcomes by a polynomial-time classical controller, at most
polynomially many operations). For every such family there is one randomized classical
polynomial-time sampler `A` (fixed before `n` and `x`) such that, on input `(n, x)`:

1. every possible output is the encoding of a valid stabilizer tableau (`n` pairwise commuting,
   independent Pauli strings with phases `±1`, not generating `−I`);
2. the distribution of the state described by the output, `∏ⱼ (I + Pⱼ)/2`, equals the
   distribution of the circuit's final state `|ψ⟩⟨ψ|` on `|x⟩` (density matrices, so the
   global phase is ignored, de Wolf p.185 footnote 3). -/
theorem gottesmanKnill (F : MCCFamily) :
    ∃ A : RandPolyTimeSampler, ∀ (n : ℕ) (x : Qubits n),
      (∀ s ∈ (A.outDist (encInput n x)).support,
          ∃ T : Tableau n, IsValidTableau T ∧ s = encodeTableau T) ∧
        (A.outDist (encInput n x)).map (fun s => tableauProjector (decodeTableau n s)) =
          F.finalDist n x := by sorry

end QAlgorithms.DeWolf
