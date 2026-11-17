-- Prove2me | Theorems.Thm_QPACLarge_Supplement_theorem_3_3
-- name    : QPACLarge.Supplement.theorem_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T09:25:25.00279+00:00
-- url     : https://prove2.me/theorems/2a6c147f-327d-449e-9032-b02ca73ed798
-- title:
--   Theorem 3.3 — one quantum example gives agreement $\ge 1/2+0.001\cdot2^{-n/2}$ with probability $\ge 0.53$
-- statement:
--   There are a quantum learner $Q$ and a constant $c$ such that the following holds. $Q$ is one uniform family of quantum circuits $\{Q_n\}_{n\ge1}$ that runs in time $\mathrm{poly}(n)$, and for every $n \ge 1$ the circuit $Q_n$ uses exactly one uniform quantum random example
--   $$|\mathrm{QEX}_f\rangle = 2^{-n/2}\sum_{x\in\{0,1\}^n}|x\rangle|f(x)\rangle.$$
--   For every $n \ge 1$ and every target $f : \{0,1\}^n \to \{0,1\}$, with probability at least $0.53$ over its measurements $Q$ outputs a deterministic classical Boolean circuit $h$ of size at most $c\,n^2$ such that
--   $$
--   \Pr_{x\sim U_n}[h(x) = f(x)] \;\ge\; \frac12 + 0.001\cdot 2^{-n/2}.
--   $$
--
--   Here $U_n$ is the uniform distribution on $\{0,1\}^n$. This is Theorem 3.3 of the paper together with Theorem 1.2 Item (i), which adds the $O(n^2)$ size of $h$: a single quantum example already yields a hypothesis whose agreement exceeds $1/2$ by an exponentially small but positive margin with probability bounded away from $1/2$, which classical learners cannot do with $o(2^{n/2})$ membership queries (Theorem 4.1).
--
--   **Formalization Note** The learner is a published `QexFamily` (Clifford+T circuits acting on copies of $|\mathrm{QEX}_f\rangle$ and ancillas, the output read from designated wires as the binary code of a Boolean circuit). "Runs in time $\mathrm{poly}(n)$" is a polynomial-time computable map sending $1^n$ to the description of $Q_n$, as in the published Theorem 1.5; the description lists every gate, so the gate count is polynomial. $2^{-n/2}$ is a real power.
--
--   Differences from the source:
--   - encoding: a quantum algorithm $Q$ that runs in time $\mathrm{poly}(n)$ and uses one uniform quantum random example → a published `QexFamily` with `ex n = 1` for $n \ge 1$, Clifford+T gates, output read from designated wires in the binary prefix-free circuit code, and a polynomial-time computable $g$ with $g(1^n)$ = the description of $Q_n$; reason: the model of Section 2.3, p.16 (at most $T(n)$ gates, description printed in time $T(n)$); the description lists every gate, so the gate count is polynomial; the paper fixes no gate set
--   - encoding: size $O(n^2)$ (Theorem 1.2(i)) → one constant $c \in \mathbb N$ with size $\le c\,n^2$ for every $n \ge 1$, inside the success event; reason: the meaning of $O(n^2)$ on $n \ge 1$
-- source:
--   Oliveira, Unconditional Quantum PAC Learning Advantage in the Large Error Regime, arXiv:2610.23268 (held file sha256 e749e7c9…), Theorem 3.3, p.25 (and Theorem 1.2 Item (i), p.5; algorithm Q: Section 3.2.2, pp.23–25)

import Mathlib
import Definitions.Def_QAlgorithms_ClassicalUnaryInput
import Definitions.Def_QPACLarge_QexFamily
import Definitions.Def_QPACLarge_QexFamily_code
import Definitions.Def_QPACLarge_QexFamily_success
import Definitions.Def_QPACLarge_agreement

namespace QPACLarge.Supplement

open QAlgorithms QAlgorithms.Complexity QPACLarge

/-- **Theorem 3.3 (Correctness of the Quantum Learner Q)**, together with **Theorem 1.2 Item (i)**.
Oliveira, *Unconditional Quantum PAC Learning Advantage in the Large Error Regime*,
arXiv:2610.23268 (held file sha256 e749e7c9…), Theorem 3.3, p.25: "For every `n ≥ 1` and every
target function `f : {0,1}ⁿ → {0,1}`, `Q` uses one uniform quantum random example and runs in time
`poly(n)`. With probability `p⋆ ≥ 0.53`, it outputs a deterministic classical Boolean circuit `h`
such that `Pr_{x∼Uₙ}[h(x) = f(x)] ≥ 1/2 + a₀ · 2^{−n/2}`, where `a₀ = 0.001`." Theorem 1.2 Item (i),
p.5, adds that `h` has size `O(n²)`.

There are a quantum learner `Q` (one family of Clifford+T circuits, `QexFamily`, acting on copies
of `|QEX_f⟩`), a polynomial-time machine printing the description of `Q_n` from `1ⁿ`, and a
constant `c`, such that for every `n ≥ 1` the circuit `Q_n` uses exactly one quantum random example
and, for every target `f`, with probability at least `0.53` it outputs a well-formed Boolean circuit
`h` with at most `c·n²` gates and `agreement(f, h) ≥ 1/2 + 0.001 · 2^{−n/2}`.

**Formalization Note.** "Runs in time `poly(n)`" (p.16: at most `T(n)` gates, description printed
in time `T(n)`) is rendered as in the published `QPACLarge.theorem_1_5`: a polynomial-time
computable `g` with `g(1ⁿ) = Q.code n`; the code lists every gate, so the gate count is polynomial.
`O(n²)` is one constant `c` with size `≤ c·n²` for all `n ≥ 1`. `2^{−n/2}` is `Real.rpow`. -/
theorem theorem_3_3 :
    ∃ (L : QexFamily ℕ (fun n => n)) (c : ℕ),
      (∃ g : Str → Str, PolyTimeComputable g ∧ ∀ n : ℕ, g (unary n) = L.code n) ∧
      ∀ n : ℕ, 1 ≤ n → L.ex n = 1 ∧
        ∀ f : Qubits n → Bool,
          (53 / 100 : ℝ) ≤ L.success n f (fun h => h.size ≤ c * n ^ 2 ∧
            1 / 2 + 1 / 1000 * (2 : ℝ) ^ (-(n : ℝ) / 2) ≤ agreement f fun x => h.eval x 0) := by sorry

end QPACLarge.Supplement
