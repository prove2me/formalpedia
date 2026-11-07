-- Prove2me | Theorems.Thm_QLocalCert_theorem_29
-- name    : QLocalCert.theorem_29
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:42:47.8409+00:00
-- url     : https://prove2.me/theorems/8564f9bc-6abb-4b38-969d-7bfab6706d9d
-- title:
--   Theorem 29 — every $\mu$-round dMA protocol for $\mathrm{TreeEQ}_\mu$ needs $\Omega(n/(\mu\log^2n))$ certificate bits
-- statement:
--   There is a constant $C>0$ such that for every $\mu\ge1$ and all $c,s$ with $0\le s<c\le1$ and $2c-1>s$ there is $N_0$ with the following property. For every even $N\ge N_0$, with $n=n_\mu(N)$, every identifier bound $U\ge n$, every $b$ and every $\mu$-round dMA protocol on $n$-node networks that decides $\mathrm{TreeEQ}_\mu$ with certificates of at most $b$ bits, completeness $c$ and soundness error $s$,
--   $$
--   b\ \ge\ C\,\frac{n}{\mu\log_2^2n}.
--   $$
--   The protocol may use private and public randomness with arbitrary laws and messages of unrestricted size.
--
--   It is the classical lower bound (B) of Theorem 1.
--
--   Differences from the source:
--   - reading: worst-case certificate size Ω(n/(µ log² n)) bits → b ≥ C n/(µ log₂² n) at every instance size n = n_µ(N), N even ≥ N₀(µ, c, s), C > 0 before µ, c, s; reason: the literal reading for every large n is false: for n = n_µ(N) + 1 no n-vertex graph is in TreeEQµ (Fact 1), and rejecting everything with 0 bits is correct
--   - generalization: µ-round dMA protocol with private randomness → private samples i.i.d. from an arbitrary law plus a public sample, arbitrary state and message types; reason: the paper claims the lower bound with public randomness (p.16); private fair coins are a special case
--   - generalization: identifier bound U = n^{O(1)} → every U ≥ n; reason: specializes to every polynomial bound U ≥ n
--   - encoding: certificates of at most b bits → List Bool certificates of length ≤ b at every node; reason: the count on p.43 includes all strings of length ≤ b
-- source:
--   Jauregui, Miyamoto, Quantum Advantage in Local Certification of Graph Properties, STOC 2027 submission (manuscript sha256 b707143b1ab5511bef4c2b77e1b803f28b32cced25a008516898fd11d28c0451), Theorem 29 and its proof, pp.42–44

import Mathlib
import Definitions.Def_QLocalCert_DMA
import Definitions.Def_QLocalCert_TreeEQ
import Definitions.Def_QLocalCert_order

set_option autoImplicit false

namespace QLocalCert

/-- **Theorem 29** (p.42). "For every fixed integer µ ≥ 1, any µ-round dMA protocol for TreeEQµ with
completeness c and soundness error s such that 2c−1 > s has worst-case certificate size
Ω(n/(µ log² n)) bits. The implicit constant is independent of µ."

Source: B. Jauregui, M. Miyamoto, *Quantum Advantage in Local Certification of Graph Properties*,
STOC 2027 submission (manuscript sha256 b707143b…0c51), Theorem 29 and its proof, pp.42–44.

**Formalization Note.**
* `Ω(n/(µ log² n))` is read along the instance sizes `n = n_µ(N) = order µ N` (Fact 1), the sizes
  on which TreeEQµ has members: there is `C > 0` chosen before `µ`, `c`, `s`, and for each
  `µ, c, s` a threshold `N₀`, such that for every even `N ≥ N₀`, every identifier bound `U ≥ n`,
  every `b` and every `µ`-round dMA protocol that decides TreeEQµ on `n`-node instances with
  certificates of at most `b` bits, completeness `c` and soundness error `s`, we have
  `b ≥ C n / (µ log₂² n)`. At other sizes no graph has the property and zero bits suffice.
* `0 ≤ s < c ≤ 1` are the standing conditions of Definition 7 (p.16).
* The dMA model allows private and public randomness with arbitrary laws, and arbitrary state and
  message types (Definition 7; `DMA`). -/
theorem theorem_29 :
    ∃ C : ℝ, 0 < C ∧ ∀ μ : ℕ, 1 ≤ μ → ∀ c s : ℝ, 0 ≤ s → s < c → c ≤ 1 → s < 2 * c - 1 →
      ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → Even N → ∀ U : ℕ, order μ N ≤ U →
        ∀ (b : ℕ) (P : DMA (order μ N) U μ), P.Correct (TreeEQ μ) b c s →
          C * (order μ N : ℝ) / (μ * Real.logb 2 (order μ N) ^ 2) ≤ b := by sorry

end QLocalCert
