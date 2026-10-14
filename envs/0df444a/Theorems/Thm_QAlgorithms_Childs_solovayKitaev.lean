-- Prove2me | Theorems.Thm_QAlgorithms_Childs_solovayKitaev
-- name    : QAlgorithms.Childs.solovayKitaev
-- status  : Open
-- author  : @Goku
-- created : 2026-10-13T17:31:37.732015+00:00
-- url     : https://prove2.me/theorems/a447439a-f2ff-42fb-ac9f-fd833779578a
-- title:
--   Solovay–Kitaev: gate-set independence with polylogarithmic overhead
-- statement:
--   Let $\mathcal A$ and $\mathcal B$ be two sets of unitary one- and two-qubit gates. Assume each set is universal: every unitary on $k$ qubits can be approximated, up to a global phase and to any precision in the spectral norm, by a circuit of gates from the set. Assume also that each set is closed under inverses ($g\in\mathcal A\Rightarrow g^\dagger\in\mathcal A$, and likewise for $\mathcal B$).
--
--   Then there are constants $C>0$ and $c\in\mathbb N$, depending only on $\mathcal A$ and $\mathcal B$, with the following property. Let $n\ge 0$, let $U=U_t\cdots U_1$ be the unitary of a circuit of $t$ gates from $\mathcal A$ acting on $n$ qubits, and let $\epsilon>0$. Then there is a circuit over $\mathcal B$ on the same $n$ qubits, with unitary $V$ and at most
--
--   $$
--   C\, t\, \bigl(\log(2+t/\epsilon)\bigr)^{c}
--   $$
--
--   gates, such that for some $\theta\in\mathbb R$
--
--   $$
--   \|U-e^{i\theta}V\|\le\epsilon .
--   $$
--
--   Here $\|\cdot\|$ is the spectral norm. In words, any $t$-gate circuit over one universal gate set can be simulated to precision $\epsilon$ with $t\cdot\mathrm{poly}(\log(t/\epsilon))$ gates from the other. So the choice of universal gate set changes running times by at most polylogarithmic factors.
--
--   **Formalization Note** The term $\mathrm{poly}(\log(t/\epsilon))$ is written as $C(\log(2+t/\epsilon))^c$ so that the bound stays meaningful when $t/\epsilon\le 1$. Both universality and precision are taken up to a global phase, as the source says on p. 16. The source's example gate set $\{H,T,\mathrm{CNOT}\}$ is universal only in this sense. The source's parenthetical claim, that a classical algorithm finds the circuit in time $t\cdot\mathrm{poly}(\log(t/\epsilon))$, is not formalized: the source fixes no machine model or encoding for gates with complex entries.
-- source:
--   Andrew Childs, Lecture Notes on Quantum Algorithms, 17 April 2025, PDF p. 15, Theorem 2.1. https://www.cs.umd.edu/~amchilds/qa/qa.pdf

import Definitions.Def_QAlgorithms_Defs_Circuit
set_option autoImplicit false

namespace QAlgorithms.Childs

open QAlgorithms

/-- Childs, Theorem 2.1 (Solovay–Kitaev), PDF p. 15. Fix two universal gate sets `A`, `B` of
unitary 1- and 2-qubit gates, both closed under inverses. Then there are constants `C > 0` and
`c` (depending only on `A` and `B`) such that every `t`-gate circuit over `A` on `n` qubits can be
implemented to precision `ϵ` (spectral norm, up to a global phase) by a circuit over `B` on the
same `n` qubits with at most `C · t · (log (2 + t/ϵ))^c` gates, i.e. `t · poly(log (t/ϵ))` gates.

The parenthetical clause of the source (a classical algorithm finds this circuit in time
`t · poly(log t/ϵ)`) is not formalized: the source fixes no classical machine model or encoding
for gates with real or complex entries, and leaves its proof as an exercise (PDF p. 17). -/
theorem solovayKitaev (A B : Set Gate)
    (hA_arity : ∀ g ∈ A, g.arity = 1 ∨ g.arity = 2) (hB_arity : ∀ g ∈ B, g.arity = 1 ∨ g.arity = 2)
    (hA_unit : ∀ g ∈ A, g.IsUnitary) (hB_unit : ∀ g ∈ B, g.IsUnitary)
    (hA_univ : IsUniversal A) (hB_univ : IsUniversal B)
    (hA_inv : ClosedUnderInverse A) (hB_inv : ClosedUnderInverse B) :
    ∃ C : ℝ, 0 < C ∧ ∃ c : ℕ, ∀ (n : ℕ) (circ : Circuit A n) (ε : ℝ), 0 < ε →
      ∃ circ' : Circuit B n,
        (circ'.size : ℝ) ≤ C * circ.size * Real.log (2 + circ.size / ε) ^ c ∧
        ApproxUpToPhase circ.unitary circ'.unitary ε := by
  sorry



end QAlgorithms.Childs
