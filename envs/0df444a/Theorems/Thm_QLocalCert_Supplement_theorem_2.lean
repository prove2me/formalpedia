-- Prove2me | Theorems.Thm_QLocalCert_Supplement_theorem_2
-- name    : QLocalCert.Supplement.theorem_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T06:41:41.52691+00:00
-- url     : https://prove2.me/theorems/b86a725a-4b07-4473-8ba2-e43def320c5d
-- title:
--   Theorem 2 — graph symmetry has one-round dQMA certificates of $O(n^{5/3}(\log n)^{7/3})$ qubits
-- statement:
--   Let identifiers be polynomially bounded: for every exponent $k\ge1$ there is a constant $C$ such that for every number of nodes $n\ge1$ and every identifier bound $U$ with $n\le U\le n^k$ there is a one-round dQMA protocol on $n$-node networks with identifiers in $[U]$ that decides $\mathrm{SYM}$ (existence of a nontrivial automorphism) with
--
--   1. **perfect completeness:** on every connected symmetric graph, with every identifier and port assignment, some certificate state is accepted with probability $1$;
--   2. **soundness error $1/3$:** on every connected asymmetric graph, every certificate state (arbitrarily entangled across the nodes) is accepted with probability at most $1/3$;
--   3. **certificate size:** each node receives at most
--   $$
--   C\, n^{5/3}(\log_2 n)^{7/3}
--   $$
--   qubits.
--
--   Classical one-round dMA protocols for $\mathrm{SYM}$ need $\Omega(n^2)$ bits, so this is a polynomial quantum advantage for a natural graph property without inputs.
--
--   **Formalization Note** The model is the published one-round dQMA model of the mission (uniform certificate size per node; local operations depend on the node's identifier and degree). The protocol writes identifier values into its certificates, so the identifier bound $U=n^{O(1)}$ enters through the exponent $k$, on which $C$ may depend.
--
--   Differences from the source:
--   - reading: U = n^{O(1)} (§2.1, p.15), O(·) constant → for every k ≥ 1 one constant C, valid for all n ≤ U ≤ n^k; reason: the paper's identifier convention; the protocol's certificates contain identifier values, so the constant depends on the polynomial degree of U
--   - encoding: O(n^{5/3}(log n)^{7/3}) qubits per node → C·n^{5/3}(log₂ n)^{7/3} for all n ≥ 1; reason: big-O as one constant; at n = 1 no instance is symmetric and a 0-qubit always-rejecting protocol satisfies the bound
-- source:
--   Jauregui, Miyamoto, Quantum Advantage in Local Certification of Graph Properties, STOC 2027 submission (manuscript sha256 b707143b1ab5511bef4c2b77e1b803f28b32cced25a008516898fd11d28c0451), Theorem 2, p.5, restated p.48; proof pp.45–49 (Lemma 30, Protocol 2); identifier bound U = n^{O(1)}, §2.1, p.15

import Mathlib
import Definitions.Def_QLocalCert_DQMA1
import Definitions.Def_QLocalCert_Supplement_SYM

set_option autoImplicit false

namespace QLocalCert.Supplement

/-- **Theorem 2** (Quantum advantage for graph symmetry; stated p.5, restated and proved p.48). "The
graph symmetry problem SYM admits a one-round dQMA protocol with perfect completeness, soundness
error 1/3, and certificates with O(n^{5/3}(log n)^{7/3}) qubits per node."

Source: B. Jauregui, M. Miyamoto, *Quantum Advantage in Local Certification of Graph Properties*,
STOC 2027 submission (manuscript sha256 b707143b…0c51), Theorem 2, p.5 and p.48; proof pp.45–49
(Lemma 30 and Protocol 2); identifier bound `U = n^{O(1)}`, §2.1, p.15.

**Formalization Note.**
* The model is the published one-round dQMA model `QLocalCert.DQMA1 n U` with its correctness
  `DQMA1.Correct` (every connected graph on `Fin n`, every injective identifier map into `Fin U`,
  every port numbering; soundness against every density operator on the joint certificate space).
  `P.cert` is the number of certificate qubits per node.
* Identifiers are bounded by `U = n^{O(1)}` (p.15) and the protocol writes identifier values into
  certificates, so the constant depends on the exponent: for every `k ≥ 1` there is `C` such that for
  all `n ≥ 1` and all `U` with `n ≤ U ≤ n^k` a protocol exists.
* `log` is `Real.logb 2`; real powers are `Real.rpow`. -/
theorem theorem_2 :
    ∀ k : ℕ, 1 ≤ k → ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n → ∀ U : ℕ, n ≤ U → U ≤ n ^ k →
      ∃ P : DQMA1 n U,
        (P.cert : ℝ) ≤ C * (n : ℝ) ^ ((5 : ℝ) / 3) * Real.logb 2 n ^ ((7 : ℝ) / 3) ∧
        P.Correct SYM 1 (1 / 3) := by sorry

end QLocalCert.Supplement
