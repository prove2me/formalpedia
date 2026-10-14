-- Prove2me | Theorems.Thm_QAlgorithms_DeWolf_bernsteinVazirani_exact
-- name    : QAlgorithms.DeWolf.bernsteinVazirani_exact
-- status  : Open
-- author  : @Goku
-- created : 2026-10-13T17:29:24.703554+00:00
-- url     : https://prove2.me/theorems/0edcd87f-04cf-4e0a-b65f-e0cd56dc721b
-- title:
--   Bernstein–Vazirani: one phase query recovers the hidden string
-- statement:
--   This is the correctness of the Bernstein–Vazirani algorithm.
--
--   Let $n \ge 0$ and $N = 2^n$, and fix a hidden string $a \in \{0,1\}^n$. The input $x \in \{0,1\}^N$ is given by $x_i = (i \cdot a) \bmod 2$ for every $i \in \{0,1\}^n$, where $i \cdot a = \sum_{k=1}^n i_k a_k$. With the phase query $O_{x,\pm} : |i\rangle \mapsto (-1)^{x_i}|i\rangle$ and the $n$-qubit Hadamard transform $H^{\otimes n}$, the Deutsch–Jozsa circuit gives
--
--   $$
--   H^{\otimes n} \, O_{x,\pm} \, H^{\otimes n} \, |0^n\rangle = |a\rangle .
--   $$
--
--   In particular, measuring the final state in the computational basis yields $a$ with probability $1$.
--
--   So one query and $2n$ Hadamard gates (the $O(n)$ other operations) recover $a$ exactly. Only the query depends on the input. Classically, $n$ queries are needed.
--
--   **Formalization Note** The input $x$ is `bvInput a`, i.e. $i \mapsto i\cdot a \bmod 2$. The circuit is the same fixed definition `deutschJozsaState` as in the Deutsch–Jozsa statement. The state equality is exact, with no global phase: the source says the result is the classical state $|a\rangle$, and that is what the computation gives.
-- source:
--   Ronald de Wolf, Quantum Computing: Lecture Notes, 27 August 2026, PDF p. 31, §2.4.2. https://homepages.cwi.nl/~rdewolf/qcnotes.pdf

import Definitions.Def_QAlgorithms_Defs_Query
set_option autoImplicit false

namespace QAlgorithms.DeWolf


/-- de Wolf §2.4.2 (PDF p. 31), the Bernstein–Vazirani algorithm: for every `n` and every hidden
string `a ∈ {0,1}^n`, on the input `x_i = (i · a) mod 2` the Deutsch–Jozsa circuit
`H^{⊗n} O_{x,±} H^{⊗n}` maps `|0^n⟩` to the basis state `|a⟩`, so the final measurement yields
`a` with probability `1` (one phase query, `2n` Hadamard gates). -/
theorem bernsteinVazirani_exact (n : ℕ) (a : Qubits n) :
    deutschJozsaState (bvInput a) = ket a ∧ prob (deutschJozsaState (bvInput a)) a = 1 := by
  sorry

end QAlgorithms.DeWolf
