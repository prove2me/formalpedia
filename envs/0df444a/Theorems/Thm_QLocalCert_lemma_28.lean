-- Prove2me | Theorems.Thm_QLocalCert_lemma_28
-- name    : QLocalCert.lemma_28
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:42:52.315488+00:00
-- url     : https://prove2.me/theorems/7ac2aad5-70a5-4628-b6a1-efa909bb178e
-- title:
--   Lemma 28 — $\mathrm{TreeEQ}_\mu$ has a one-round dQMA protocol with $O(\mu\log n)$ qubits, constant independent of $\mu$
-- statement:
--   There is a constant $C$ such that for every $\mu\ge1$, every $n\ge1$ and every identifier bound $U\ge n$ there is a one-round dQMA protocol on $n$-node networks that decides $\mathrm{TreeEQ}_\mu$ with completeness $1$ and soundness error $\tfrac13$, on every instance and against every (arbitrarily entangled) certificate state, with at most $C\mu\log_2n$ certificate qubits per node and at most $C\mu\log_2n$ qubits per message.
--
--   It is the quantum upper bound (A) of Theorem 1, with the message size added.
--
--   Differences from the source:
--   - encoding: O(µ log n) qubits, implicit constant independent of µ → cert ≤ C µ log₂ n and msg ≤ C µ log₂ n with C before µ, n ≥ 1, U ≥ n; reason: big-O as one constant chosen before µ
--   - generalization: identifier bound U = n^{O(1)} → every U ≥ n; reason: no certificate carries an identifier; specializes to every polynomial bound U ≥ n
-- source:
--   Jauregui, Miyamoto, Quantum Advantage in Local Certification of Graph Properties, STOC 2027 submission (manuscript sha256 b707143b1ab5511bef4c2b77e1b803f28b32cced25a008516898fd11d28c0451), Lemma 28 and its proof, pp.40–42

import Mathlib
import Definitions.Def_QLocalCert_DQMA1
import Definitions.Def_QLocalCert_TreeEQ

set_option autoImplicit false

namespace QLocalCert

/-- **Lemma 28** (p.40). "For every fixed integer µ ≥ 1, the property TreeEQµ admits a one-round
dQMA protocol on connected n-vertex graphs with perfect completeness, soundness error at most 1/3,
and O(µ log n) certificate qubits per node and qubits per individual message. The implicit
constant is independent of µ; for fixed µ this is O(log n)."

Source: B. Jauregui, M. Miyamoto, *Quantum Advantage in Local Certification of Graph Properties*,
STOC 2027 submission (manuscript sha256 b707143b…0c51), Lemma 28 and its proof, pp.40–42.

**Formalization Note.** `O(µ log n)` is one constant `C` chosen before `µ`, `n` and `U`, for
every `µ ≥ 1`, every `n ≥ 1` and every identifier bound `U ≥ n`. The protocol (`DQMA1`, from
Definitions 7 and 18) has `cert ≤ C µ log₂ n` certificate qubits per node and `msg ≤ C µ log₂ n`
qubits per directed-edge message, completeness 1 and soundness error 1/3 against every density
operator on the joint certificate space, on every instance. -/
theorem lemma_28 :
    ∃ C : ℝ, ∀ μ : ℕ, 1 ≤ μ → ∀ n : ℕ, 1 ≤ n → ∀ U : ℕ, n ≤ U →
      ∃ P : DQMA1 n U, (P.cert : ℝ) ≤ C * μ * Real.logb 2 n ∧
        (P.msg : ℝ) ≤ C * μ * Real.logb 2 n ∧ P.Correct (TreeEQ μ) 1 (1 / 3) := by sorry

end QLocalCert
