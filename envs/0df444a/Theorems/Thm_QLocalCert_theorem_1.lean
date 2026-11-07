-- Prove2me | Theorems.Thm_QLocalCert_theorem_1
-- name    : QLocalCert.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:42:51.772009+00:00
-- url     : https://prove2.me/theorems/4a804672-41be-46b4-acb3-44302fbb0fd9
-- title:
--   Theorem 1 — $\mathrm{TreeEQ}_\mu$: one-round dQMA with $O(\mu\log n)$ qubits, while $\mu$-round dMA needs $\Omega(n/(\mu\log^2n))$ bits
-- statement:
--   Let $\mathrm{TreeEQ}_\mu$ be the graph property of §4: trees isomorphic to $T^{\mathrm{tr}}_{N,\mu}(z,z)$ for an even $N\ge8$ and a balanced $z\in\{0,1\}^N$.
--
--   **(A) Quantum upper bound.** There is a constant $C$, independent of $\mu$, such that for every $\mu\ge1$, every $n\ge1$ and every identifier bound $U\ge n$ there is a one-round dQMA protocol on $n$-node networks that decides $\mathrm{TreeEQ}_\mu$ with perfect completeness and soundness error $\tfrac13$, on every instance and against every (arbitrarily entangled) certificate state, using at most
--   $$
--   C\,\mu\log_2n
--   $$
--   certificate qubits per node.
--
--   **(B) Classical lower bound.** There is a constant $C>0$, independent of $\mu$, such that for every $\mu\ge1$ and all $c,s$ with $0\le s<c\le1$ and $2c-1>s$ there is $N_0$ such that for every even $N\ge N_0$, with $n=n_\mu(N)$ the order of the trees $T^{\mathrm{tr}}_{N,\mu}$, every $U\ge n$ and every $\mu$-round dMA protocol on $n$-node networks that decides $\mathrm{TreeEQ}_\mu$ with certificates of at most $b$ bits, completeness $c$ and soundness error $s$,
--   $$
--   b\ \ge\ C\,\frac{n}{\mu\log_2^2n}.
--   $$
--
--   For fixed $\mu$ this is an exponential separation between quantum and classical certificate sizes, measured in the number of vertices, for a graph property without inputs.
--
--   Differences from the source:
--   - reading: there exists a graph property TreeEQµ → the statement for the property TreeEQµ constructed in §4 (p.37); reason: the theorem names the property built in Section 4; this implies the printed existential
--   - encoding: O(µ log n) qubits, implicit constant independent of µ → cert ≤ C µ log₂ n, C before µ, for every n ≥ 1 and U ≥ n; reason: big-O as one constant chosen before µ
--   - generalization: identifier bound U = n^{O(1)} → every U ≥ n in (A) and (B); reason: specializes to every polynomial bound U ≥ n
--   - reading: certificates of Ω(n/(µ log² n)) bits → b ≥ C n/(µ log₂² n) at every instance size n = n_µ(N), N even ≥ N₀(µ, c, s), C > 0 before µ, c, s; reason: the literal reading for every large n is false: at n = n_µ(N) + 1 no graph has the property and 0 bits suffice
--   - generalization: µ-round dMA protocol (private randomness) → private samples from an arbitrary law plus a public sample, arbitrary state and message types; reason: the paper claims its classical lower bounds with public randomness (p.16); private fair coins are a special case
--   - encoding: certificates of at most b bits → List Bool certificates of length ≤ b; reason: the count on p.43 includes all strings of length ≤ b
-- source:
--   Jauregui, Miyamoto, Quantum Advantage in Local Certification of Graph Properties, STOC 2027 submission (manuscript sha256 b707143b1ab5511bef4c2b77e1b803f28b32cced25a008516898fd11d28c0451), Theorem 1, p.5; proof in §4 via Lemma 28 and Theorem 29, p.40

import Mathlib
import Definitions.Def_QLocalCert_DQMA1
import Definitions.Def_QLocalCert_DMA
import Definitions.Def_QLocalCert_TreeEQ
import Definitions.Def_QLocalCert_order

set_option autoImplicit false

namespace QLocalCert

/-- **Theorem 1** (Exponential quantum advantage for TreeEQµ, p.5). "Let µ ≥ 1 be a fixed positive
integer. There exists a graph property TreeEQµ that admits a one-round dQMA protocol with perfect
completeness, soundness error 1/3, and certificates with O(µ log n) qubits. The implicit constant
is independent of µ. In contrast, every µ-round dMA protocol for TreeEQµ with completeness c and
soundness error s satisfying 2c − 1 > s requires certificates of Ω(n/(µ log² n)) bits."

Source: B. Jauregui, M. Miyamoto, *Quantum Advantage in Local Certification of Graph Properties*,
STOC 2027 submission (manuscript sha256 b707143b…0c51), Theorem 1, p.5; proved in §4 "by combining the quantum upper bound of Lemma 28 with
the classical lower bound of Theorem 29" (p.40).

**Formalization Note.**
* The property is the TreeEQµ constructed in §4 (Definition 23, p.37), which implies the printed
  "there exists a graph property".
* (A) One constant `C` before `µ`: for every `µ ≥ 1`, every `n ≥ 1` and every identifier
  bound `U ≥ n` there is a one-round dQMA protocol (`DQMA1`, Definitions 7 and 18) on `n`-node
  networks with at most `C µ log₂ n` certificate qubits per node, completeness 1 and soundness
  error 1/3, correct on every instance (every connected graph, identifier and port assignment)
  against every density operator on the joint certificate space.
* (B) `Ω(n/(µ log² n))` along the instance sizes `n = order µ N` of TreeEQµ (Fact 1), with
  `C > 0` before `µ, c, s` and `N₀` after them; for every `U ≥ n` and every `µ`-round dMA protocol
  (private and public randomness, arbitrary laws, unrestricted messages) with certificates of at
  most `b` bits that is correct with completeness `c` and soundness `s`. At sizes outside the
  sequence `order µ N` no graph has the property, so no lower bound holds there.
* `log` is `Real.logb 2`. -/
theorem theorem_1 :
    (∃ C : ℝ, ∀ μ : ℕ, 1 ≤ μ → ∀ n : ℕ, 1 ≤ n → ∀ U : ℕ, n ≤ U →
      ∃ P : DQMA1 n U, (P.cert : ℝ) ≤ C * μ * Real.logb 2 n ∧
        P.Correct (TreeEQ μ) 1 (1 / 3)) ∧
    (∃ C : ℝ, 0 < C ∧ ∀ μ : ℕ, 1 ≤ μ → ∀ c s : ℝ, 0 ≤ s → s < c → c ≤ 1 → s < 2 * c - 1 →
      ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → Even N → ∀ U : ℕ, order μ N ≤ U →
        ∀ (b : ℕ) (P : DMA (order μ N) U μ), P.Correct (TreeEQ μ) b c s →
          C * (order μ N : ℝ) / (μ * Real.logb 2 (order μ N) ^ 2) ≤ b) := by sorry

end QLocalCert
