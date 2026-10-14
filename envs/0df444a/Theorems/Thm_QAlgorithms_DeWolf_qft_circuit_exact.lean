-- Prove2me | Theorems.Thm_QAlgorithms_DeWolf_qft_circuit_exact
-- name    : QAlgorithms.DeWolf.qft_circuit_exact
-- status  : Open
-- author  : @Goku
-- created : 2026-10-13T17:34:29.597572+00:00
-- url     : https://prove2.me/theorems/550be475-3355-4489-84c2-87d21518f788
-- title:
--   The n-qubit QFT has an exact circuit of at most n^2 Hadamard, controlled-R_s and swap gates
-- statement:
--   Let $n\ge 0$ and $N=2^n$. The quantum Fourier transform $F_N$ is the $N\times N$ unitary matrix with $(j,k)$-entry $\frac{1}{\sqrt N}\,\omega_N^{jk}$, where $\omega_N=e^{2\pi i/N}$ and rows and columns are indexed by $0,\dots,N-1$; it acts on $n$ qubits via the identification $|k\rangle=|k_1\dots k_n\rangle$ with $k_1$ the most significant bit.
--
--   Consider the gate set consisting of the Hadamard gate $H$, the controlled-$R_s$ gates ($s\ge 1$) with
--
--   $$
--   R_s=\begin{pmatrix}1&0\\0&e^{2\pi i/2^s}\end{pmatrix},
--   $$
--
--   and the two-qubit swap gate, each gate placed on any (ordered) choice of distinct qubits. Then there is a quantum circuit $C$ on $n$ qubits over this gate set whose unitary equals the Fourier transform exactly and which has at most $n^2$ gates:
--
--   $$
--   U_C = F_{2^n}, \qquad |C|\le n^2 .
--   $$
--
--   In particular the QFT can be implemented with $O(n^2)$ elementary gates, exponentially fewer than the $O(N\log N)$ steps of the classical FFT. This circuit is the basic building block of phase estimation, period finding and Shor's algorithm.
--
--   **Formalization Note** The gate set is the shared `qftGateSet` ($H$, controlled-$R_s$ for all $s\ge1$, swap); the size of a circuit is its number of gates. The equality is exact matrix equality, not equality up to a global phase. At $n=0$ the statement says the empty circuit implements $F_1=(1)$.
-- source:
--   Ronald de Wolf, Quantum Computing: Lecture Notes, 27 August 2026, PDF p. 45, §4.5. https://homepages.cwi.nl/~rdewolf/qcnotes.pdf

import Definitions.Def_QAlgorithms_Defs_Fourier
set_option autoImplicit false

namespace QAlgorithms.DeWolf

/-- de Wolf §4.5, PDF pp.44–45 (unnumbered): the `n`-qubit quantum Fourier transform `F_{2^n}`
(entries `ω_N^{jk}/√N`, `ω_N = e^{2πi/N}`, p.41; most significant bit first, p.44) is implemented
exactly by a circuit of Hadamards, controlled-`R_s` gates and swap gates with at most `n²` gates
("the overall circuit uses at most `n²` gates"), in particular `O(n²)` elementary gates. -/
theorem qft_circuit_exact (n : ℕ) :
    ∃ c : Circuit qftGateSet n, c.unitary = qftQubits n ∧ c.size ≤ n ^ 2 := by
  sorry


end QAlgorithms.DeWolf
