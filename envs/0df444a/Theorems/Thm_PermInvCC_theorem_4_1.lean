-- Prove2me | Theorems.Thm_PermInvCC_theorem_4_1
-- name    : PermInvCC.theorem_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T20:26:15.594304+00:00
-- url     : https://prove2.me/theorems/a2603fe1-61d7-452f-acb6-89118e0907ac
-- title:
--   Theorem 4.1 — quantum lower bound $c+1\ge a_q/h(T,U)$ for two types
-- statement:
--   For each $q\ge2$ there is $a_q>0$ with the following property. Let $T\ne U$ be two types of total $n$ with the same row and column margins. If a protocol using $c$ qubits and arbitrary prior entanglement distinguishes all inputs of type $T$ from all inputs of type $U$ with error at most $1/3$, then
--   $$c+1\ge\frac{a_q}{h(T,U)}. \tag{4.1}$$
--
--   This is the quantum half of the main theorem: $Q^*$ is at least of order $h_g^{-1}$.
--
--   Differences from the source:
--   - encoding: distinguishes type T from type U with error at most 1/3 → for an output value b: error ≤ 1/3 for b on every pair of type T and for ¬b on every pair of type U; reason: the two types must receive different outputs; either assignment is allowed
--   - reading: arbitrary prior entanglement → an arbitrary input-independent unit start state on finitely many qubits W (W unbounded); reason: the standard finite-dimensional model of entanglement-assisted communication, the one of [LS09] and [SS24, Thm 2.22] on which the paper builds its quantum bounds (App. B.3); the paper never uses an infinite-dimensional state
-- source:
--   Huang and Ye, Quantum Advantage of Permutation-Invariant Functions in Communication Complexity, arXiv:2609.40116 (held version, sha256 fe1797dd…), Theorem 4.1, p.15 (proof pp.20–21)

import Mathlib
import Definitions.Def_PermInvCC_jointType
import Definitions.Def_PermInvCC_hE
import Definitions.Def_PermInvCC_EntQProtocol

namespace PermInvCC

/-- **Theorem 4.1 (Quantum Lower Bound for Two Types)** (Y. Huang and Z. Ye, arXiv:2609.40116,
held version sha256 fe1797dd…, p.15). For each `q ≥ 2`, there is `a_q > 0` with the following
property. Let `T ≠ U` be two types of total `n` with the same row and column margins. If a
protocol using `c` qubits and arbitrary prior entanglement distinguishes all inputs of type `T`
from all inputs of type `U` with error at most `1/3`, then `c + 1 ≥ a_q / h(T, U)` (4.1).

**Formalization Note.** "Distinguishes with error at most `1/3`" means: for some output value
`b`, the output differs from `b` with probability at most `1/3` on every pair of type `T`, and
differs from `¬b` with probability at most `1/3` on every pair of type `U`. `a_q` is chosen
before `n, T, U` and the protocol. (`n ≥ 2` holds automatically: two different types with the
same margins need `n ≥ 2`.) -/
theorem theorem_4_1 (q : ℕ) (hq : 2 ≤ q) :
    ∃ aq : ℝ, 0 < aq ∧
      ∀ (n : ℕ) (T U : Fin q → Fin q → ℕ), ∑ a, ∑ b, T a b = n → ∑ a, ∑ b, U a b = n →
        T ≠ U → (∀ a, rowMargin T a = rowMargin U a) → (∀ b, colMargin T b = colMargin U b) →
        ∀ (c : ℕ) (P : EntQProtocol (Fin n → Fin q) (Fin n → Fin q)), P.cost ≤ c →
          ∀ b : Bool,
            (∀ x y, jointType x y = T → P.errQ x y b ≤ 1 / 3) →
            (∀ x y, jointType x y = U → P.errQ x y (!b) ≤ 1 / 3) →
            aq / hTU T U ≤ (c : ℝ) + 1 := by sorry

end PermInvCC
