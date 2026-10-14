-- Prove2me | Theorems.Thm_QAlgorithms_DeWolf_deutschJozsa_exact
-- name    : QAlgorithms.DeWolf.deutschJozsa_exact
-- status  : Open
-- author  : @Goku
-- created : 2026-10-13T17:28:59.894029+00:00
-- url     : https://prove2.me/theorems/d6b26b2d-85e7-4961-8639-be742ed9bfe9
-- title:
--   Deutsch–Jozsa: one phase query decides constant vs balanced with certainty
-- statement:
--   This is the correctness of the Deutsch–Jozsa algorithm.
--
--   Let $n \ge 0$ and $N = 2^n$, and let $x \in \{0,1\}^N$ be an input whose bits $x_i$ are addressed by $n$-bit indices $i \in \{0,1\}^n$. The phase query is the $n$-qubit unitary $O_{x,\pm} : |i\rangle \mapsto (-1)^{x_i} |i\rangle$, and $H^{\otimes n}$ is the Hadamard transform on $n$ qubits. Call $x$ *constant* if all $x_i$ are equal and *balanced* if exactly $N/2$ of the $x_i$ equal $1$. Let
--
--   $$
--   |\psi_x\rangle = H^{\otimes n} \, O_{x,\pm} \, H^{\otimes n} \, |0^n\rangle .
--   $$
--
--   Then, measuring $|\psi_x\rangle$ in the computational basis:
--
--   1. if $x$ is constant, the outcome is $0^n$ with probability $1$, that is $|\langle 0^n | \psi_x \rangle|^2 = 1$;
--   2. if $x$ is balanced, the outcome is $0^n$ with probability $0$, that is $|\langle 0^n | \psi_x \rangle|^2 = 0$.
--
--   So the rule "answer *constant* exactly when the outcome is $0^n$" solves the Deutsch–Jozsa problem with certainty. The circuit makes a single query, uses $2n$ Hadamard gates (the $O(n)$ other operations), and depends on $x$ only through the query.
--
--   This is the first example in the notes of an exact quantum query algorithm that beats deterministic classical algorithms, which need $N/2+1$ queries.
--
--   **Formalization Note** The input is a function from $n$-bit strings to bits. Balancedness is written $2\cdot|x| = 2^n$, with no natural-number division. At $n = 0$ no input is balanced and every input is constant. The circuit is the fixed definition `deutschJozsaState`, so the query count and the Hadamard count come from how that definition is built.
-- source:
--   Ronald de Wolf, Quantum Computing: Lecture Notes, 27 August 2026, PDF p. 31, §2.4.1. https://homepages.cwi.nl/~rdewolf/qcnotes.pdf

import Definitions.Def_QAlgorithms_Defs_Query
set_option autoImplicit false

namespace QAlgorithms.DeWolf

/-- de Wolf §2.4.1 (PDF pp. 30–31), the Deutsch–Jozsa algorithm: for every `n` and every
`x ∈ {0,1}^{2^n}` that is constant or balanced, measuring `H^{⊗n} O_{x,±} H^{⊗n} |0^n⟩` yields
`0^n` with probability `1` if `x` is constant and with probability `0` if `x` is balanced
(`2 · |x| = 2^n`). So the rule "answer constant iff the outcome is `0^n`" decides the problem
with certainty using one phase query and `2n` Hadamard gates. -/
theorem deutschJozsa_exact (n : ℕ) (x : Qubits n → Bool) :
    (IsConstant x → prob (deutschJozsaState x) (fun _ : Fin n => false) = 1) ∧
      (IsBalanced x → prob (deutschJozsaState x) (fun _ : Fin n => false) = 0) := by
  sorry


end QAlgorithms.DeWolf
