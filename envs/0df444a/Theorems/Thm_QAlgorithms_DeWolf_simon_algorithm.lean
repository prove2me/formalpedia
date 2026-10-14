-- Prove2me | Theorems.Thm_QAlgorithms_DeWolf_simon_algorithm
-- name    : QAlgorithms.DeWolf.simon_algorithm
-- status  : Open
-- author  : @Goku
-- created : 2026-10-13T17:33:48.903707+00:00
-- url     : https://prove2.me/theorems/5fda73c2-2be3-43b9-8350-47c2509bedd4
-- title:
--   Simon's algorithm: uniform orthogonal samples, expected O(n) queries, O(n^3) classical post-processing
-- statement:
--   This is the analysis of Simon's algorithm.
--
--   Let $N=2^n$ and identify $\{0,\dots,N-1\}$ with $\{0,1\}^n$; write $i\oplus s$ for bitwise addition modulo $2$ and $s\cdot j=\sum_k s_kj_k \bmod 2$. An input is $x=(x_i)_{i\in\{0,1\}^n}$ with $x_i\in\{0,1\}^n$, and Simon's promise says there is a nonzero $s\in\{0,1\}^n$ with $x_i=x_j \iff (i=j \text{ or } i=j\oplus s)$. A query is the unitary $O_x:|i,y\rangle\mapsto|i,y\oplus x_i\rangle$. One run of the subroutine prepares
--
--   $$
--   |\Psi_x\rangle=(H^{\otimes n}\otimes I)\,O_x\,(H^{\otimes n}\otimes I)\,|0^n\rangle|0^n\rangle
--   $$
--
--   (one query, $2n$ Hadamard gates) and measures the first register. Then:
--
--   1. For every $n$, every $x$ and nonzero $s$ satisfying the promise, and every $j$, the outcome $j$ has probability $2^{-(n-1)}$ if $s\cdot j=0$ and $0$ otherwise; i.e. it is uniform on $\{j: s\cdot j=0\}$.
--   2. There are constants $C>0$ and $N_0$ (independent of $n$, $x$, $s$) such that for all $n\ge N_0$: if the subroutine is repeated independently until the outcomes obtained so far span a subspace of $\mathbb F_2^n$ of dimension $n-1$, the expected number of runs, which equals the expected number of $x_i$-queries, is at most $C\,n$.
--   3. If outcomes $j_1,\dots,j_m$ are all orthogonal to $s$ and span a subspace of dimension at least $n-1$, then the only nonzero solution $y$ of the system $j_k\cdot y=0$ $(k=1,\dots,m)$ is $y=s$.
--   4. There are constants $C>0$ and $N_0$ such that for every $n\ge N_0$ there is a classical Boolean circuit (AND, OR, NOT gates of fan-in at most $2$) of size at most $C n^3$ which, given any $n-1$ linearly independent strings $j_1,\dots,j_{n-1}$ orthogonal to a nonzero $s$, outputs $s$.
--
--   Together these say that Simon's algorithm finds $s$ with an expected $O(n)$ queries and polynomially many other operations, an exponential speed-up over classical randomized algorithms.
--
--   **Formalization Note** Item 2 uses the expected stopping time of an i.i.d. sequence drawn from the PMF whose masses are the first-register marginals of $|\Psi_x\rangle$; its existence is part of the conclusion. The intermediate measurement of the second register is omitted, as the source allows. The constant $N_0$ in item 4 also absorbs $n=1$, where a circuit with no input wires cannot output the constant $1$. The $n-1$ input strings are fed to the circuit row-major through $\mathrm{finProdFinEquiv}$.
-- source:
--   Ronald de Wolf, Quantum Computing: Lecture Notes, 27 August 2026, PDF p. 36, §3.2. https://homepages.cwi.nl/~rdewolf/qcnotes.pdf

import Definitions.Def_QAlgorithms_Defs_Query
import Definitions.Def_QAlgorithms_DeWolf_Ch03_Model
set_option autoImplicit false

namespace QAlgorithms.DeWolf



/-- de Wolf §3.2 (PDF pp. 35–36), Simon's algorithm. For every `n`, every input
`x : {0,1}^n → {0,1}^n` and every nonzero `s` with Simon's promise
(`x_i = x_j ⟺ i = j ∨ i = j ⊕ s`):

1. one run of the subroutine (`|0^n⟩|0^n⟩`, `H^{⊗n}` on the first register, one query,
   `H^{⊗n}` on the first register) yields first-register outcome `j` with probability
   `2/2^n = 2^{−(n−1)}` if `s · j = 0 mod 2` and `0` otherwise, i.e. a uniformly random element
   of `{j | s · j = 0 mod 2}`;
2. there are `C > 0` and `N₀`, independent of `n`, `x`, `s`, such that for `n ≥ N₀`, if the
   subroutine is repeated independently until the outcomes span a space of dimension `n − 1`,
   the expected number of runs (= expected number of `x_i`-queries, one per run) is at most
   `C · n` (the outcome distribution `μ` is the one of item 1);
3. whenever outcomes `j_1, …, j_m`, all orthogonal to `s`, span a space of dimension `≥ n − 1`,
   the only nonzero solution `y` of the equations `j_k · y = 0 mod 2` is `y = s`;
4. there are `C > 0` and `N₀` such that for every `n ≥ N₀` a classical Boolean circuit of size
   at most `C n^3` maps any `n − 1` linearly independent strings `j_1, …, j_{n−1}` orthogonal to
   a nonzero `s` to `s` (Gaussian elimination modulo 2, "a classical circuit of size roughly
   `O(n^3)`"). -/
theorem simon_algorithm :
    (∀ (n : ℕ) (x : Qubits n → Qubits n) (s : Qubits n), SimonPromise x s → s ≠ 0 →
      ∀ j : Qubits n, marginalFst (simonRunState x) j =
        if dotBits s j = false then 2 / (2 : ℝ) ^ n else 0) ∧
    (∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ n ≥ N₀, ∀ (x : Qubits n → Qubits n) (s : Qubits n),
      SimonPromise x s → s ≠ 0 →
      ∃ μ : PMF (Qubits n), (∀ j, μ j = ENNReal.ofReal (marginalFst (simonRunState x) j)) ∧
        expectedStoppingTime μ (fun _ l => n - 1 ≤ simonSpanRank l) ≤
          ENNReal.ofReal (C * n)) ∧
    (∀ (n : ℕ) (s : Qubits n), s ≠ 0 → ∀ (m : ℕ) (js : Fin m → Qubits n),
      (∀ k, dotBits s (js k) = false) → n - 1 ≤ simonSpanRank js →
      ∀ y : Qubits n, y ≠ 0 → (∀ k, dotBits (js k) y = false) → y = s) ∧
    (∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ n ≥ N₀, ∃ G : BoolCircuit ((n - 1) * n) n,
      G.WellFormed ∧ (G.size : ℝ) ≤ C * (n : ℝ) ^ 3 ∧
      ∀ (s : Qubits n), s ≠ 0 → ∀ js : Fin (n - 1) → Qubits n,
        (∀ k, dotBits s (js k) = false) →
        LinearIndependent (ZMod 2) (fun k => simonBitsToZMod2 (js k)) →
        G.eval (fun p => js (finProdFinEquiv.symm p).1 (finProdFinEquiv.symm p).2) = s) := by
  sorry


end QAlgorithms.DeWolf
