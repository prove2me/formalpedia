-- Prove2me | Theorems.Thm_QAlgorithms_DeWolf_hhl_cks_theorem2
-- name    : QAlgorithms.DeWolf.hhl_cks_theorem2
-- status  : Open
-- author  : @Goku
-- created : 2026-10-13T17:42:53.696995+00:00
-- url     : https://prove2.me/theorems/fd5d858b-53cc-4889-93a1-399948e7ce8a
-- title:
--   HHL algorithm: gate-efficient QLSP solver with O((dκ²/ε) polylog) queries to P_A and O(dκ polylog) uses of P_B
-- statement:
--   This is the complexity theorem for the Harrow–Hassidim–Lloyd (HHL) algorithm for the quantum linear systems problem (QLSP), in the form of Childs, Kothari and Somma (2017), Theorem 2.
--
--   **The problem.** Let $A$ be an $N\times N$ Hermitian, invertible matrix with operator norm $\|A\|=1$, condition number $\kappa=\sigma_{\max}(A)/\sigma_{\min}(A)$ (known to the algorithm), and at most $d$ nonzero entries in every row and every column. Let $\vec b\neq 0$ be a vector in $\mathbb C^N$ and $\vec x=A^{-1}\vec b$, and write $|b\rangle=\sum_i b_i|i\rangle/\|\vec b\|$, $|x\rangle=\sum_i x_i|i\rangle/\|\vec x\|$, with indices held in $n=\lceil\log_2 N\rceil$ qubits. The matrix is accessed through a black box $P_A$ consisting of the two unitary maps
--
--   $$|j,\ell\rangle\mapsto|j,\nu(j,\ell)\rangle\quad(j\in[N],\ \ell\in[d]),\qquad |j,k,z\rangle\mapsto|j,k,z\oplus A_{jk}\rangle\quad(j,k\in[N]),$$
--
--   where $\nu(j,\ell)$ is the row index of the $\ell$-th nonzero entry of column $j$ and the entry $A_{jk}$ is written exactly as a $b$-bit string in a fixed encoding. The vector is accessed through a unitary black box $P_B$ with $P_B|0^n\rangle=|b\rangle$. A use of a black box (possibly controlled, possibly inverted) is one query; the gate complexity is the number of other 2-qubit gates. The goal is to output, with probability at least $1/2$ and with a flag qubit indicating success, a state that is $\varepsilon$-close in Euclidean norm to $|x\rangle$.
--
--   **The theorem.** There are absolute constants $C>0$ and $c\in\mathbb N$, and for every entry encoding constants $C'>0$, $c'\in\mathbb N$, such that for all $N$, all $d\ge1$, $\kappa\ge1$ and $0<\varepsilon<1$ there is a single quantum circuit, depending only on $N,d,\kappa,\varepsilon$ and the encoding, which solves every QLSP instance with these parameters, and whose number $Q$ of queries to $P_A$ and number $Q_B$ of uses of $P_B$ satisfy
--
--   $$Q\le C\,\frac{d\kappa^2}{\varepsilon}\Bigl(1+\log\frac{d\kappa}{\varepsilon}\Bigr)^{c},\qquad Q_B\le C\,d\kappa\Bigl(1+\log\frac{d\kappa}{\varepsilon}\Bigr)^{c},$$
--
--   and which is gate-efficient: its number $G$ of 2-qubit gates satisfies
--
--   $$G\le C'\,Q\,\bigl(1+\log Q+\log N\bigr)^{c'}.$$
--
--   Success means: started in $|0\cdots0\rangle$ on a flag qubit, $n$ output qubits and some number of work qubits, the final state has flag $1$ with probability $p\ge 1/2$, and the normalized flag-$1$ branch is within Euclidean distance $\varepsilon$ of $|1\rangle|x\rangle|g\rangle$ for some unit work-register state $|g\rangle$.
--
--   This is the benchmark against which the later precision improvements (Theorems 3–5 of Childs–Kothari–Somma) and de Wolf's §10.3 singular-value-transformation algorithm are measured.
--
--   **Formalization Note** A $d$-sparse matrix with $\|A\|=1$ automatically has $d\ge1$ and $\kappa\ge1$; these ranges are stated so that the logarithms are positive. The polylogarithmic factors $\mathrm{poly}(L)$ with $L>0$ are written $C(1+L)^c$, which is equivalent. The gate-efficiency constants may depend on the fixed exact encoding $\mathrm{dec}:\{0,1\}^b\to\mathbb C$ of matrix entries, because the source treats the entry representation as exact and does not account for its arithmetic; the query constants do not. The source's assumption that $P_B$ runs in time $O(\mathrm{poly}\log N)$ concerns the cost of $P_B$, which is counted only through $Q_B$. The theorem is vacuous for $d>N$ (the column map cannot exist), where the bound for $d=N$ is stronger anyway. The output may differ from $|x\rangle$ by a global phase, absorbed into the work-register state.
-- source:
--   Childs, Kothari and Somma (2017), arXiv:1511.02306v2, Problem 1 (PDF p. 3) and Theorem 2 (PDF p. 4), https://arxiv.org/abs/1511.02306v2 . Lecture context: Ronald de Wolf, Quantum Computing: Lecture Notes, section 10.2–10.3 (PDF p. 96), https://homepages.cwi.nl/~rdewolf/qcnotes.pdf .

import Definitions.Def_QAlgorithms_Defs_LinearSystems
import Definitions.Def_QAlgorithms_DeWolf_Ch10_Model
set_option autoImplicit false

namespace QAlgorithms.DeWolf



/-- **The HHL algorithm** (de Wolf §10.2–10.3, PDF p.96; stated as CKS Problem 1, p.3, and
Theorem 2, p.4): the QLSP can be solved by a gate-efficient algorithm that makes
`O((dκ²/ε) poly(log(dκ/ε)))` queries to `P_A` and `O(dκ poly(log(dκ/ε)))` uses of `P_B`.

Quantifier order: the constants `C, c` of the two query bounds are absolute (before everything);
the constants `C', c'` of the gate-efficiency bound may depend on the fixed exact encoding
`dec : {0,1}^b → ℂ` of matrix entries (CKS p.3: "we assume the entries of `A` can be represented
exactly"); then for all parameters `N, d, κ, ε` there is one oracle circuit (it may depend on
`N, d, κ, ε` and the encoding, never on `A`, `b⃗` or the oracles) that meets the three cost bounds
and succeeds on every QLSP instance with these parameters. Queries may be controlled or inverted
(each counts as one use). The output layout is a flag wire, `⌈log₂ N⌉` output wires, `m` garbage
wires, started in `|0…0⟩`; success is `QLSPSuccess` (flag probability `≥ 1/2`, flagged branch
`ε`-close to `|x⟩ ⊗ |garbage⟩`). -/
theorem hhl_cks_theorem2 :
    ∃ C : ℝ, 0 < C ∧ ∃ c : ℕ,
    ∀ (b : ℕ) (dec : Qubits b → ℂ),
    ∃ C' : ℝ, 0 < C' ∧ ∃ c' : ℕ,
    ∀ (N d : ℕ) (κ ε : ℝ), 1 ≤ d → 1 ≤ κ → 0 < ε → ε < 1 →
    ∃ (m : ℕ) (alg : OracleCircuit twoQubitGates (qlspArity N b) (1 + Nat.clog 2 N + m)),
      ((alg.queryCount 0 + alg.queryCount 1 : ℕ) : ℝ) ≤
          C * ((d : ℝ) * κ ^ 2 / ε) * (1 + Real.log ((d : ℝ) * κ / ε)) ^ c ∧
      ((alg.queryCount 2 : ℕ) : ℝ) ≤
          C * ((d : ℝ) * κ) * (1 + Real.log ((d : ℝ) * κ / ε)) ^ c ∧
      ((alg.gateCount : ℕ) : ℝ) ≤
          C' * ((alg.queryCount 0 + alg.queryCount 1 : ℕ) : ℝ) *
            (1 + Real.log ((alg.queryCount 0 + alg.queryCount 1 : ℕ) : ℝ) + Real.log (N : ℝ)) ^ c' ∧
      ∀ (A : Matrix (Fin N) (Fin N) ℂ) (bvec : EuclideanSpace ℂ (Fin N))
        (orc : (k : Fin 3) → Matrix (Qubits (qlspArity N b k)) (Qubits (qlspArity N b k)) ℂ),
        A.IsHermitian → IsUnit A → conditionNumber A = κ → specNorm A = 1 → IsSparse A d →
        bvec ≠ 0 →
        IsSparseAccessOracle A d dec (orc 0) (orc 1) →
        IsStatePrep bvec (orc 2) →
        QLSPSuccess (act (alg.unitary orc) (zeroKet (1 + Nat.clog 2 N + m)))
          (padState (Nat.clog 2 N) (normalizedVec (act A⁻¹ bvec))) ε := by
  sorry

end QAlgorithms.DeWolf
