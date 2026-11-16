-- Prove2me | Theorems.Thm_PelagicFF_Supplement_theorem_6_4
-- name    : PelagicFF.Supplement.theorem_6_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T21:30:50.790845+00:00
-- url     : https://prove2.me/theorems/e75d5898-ea45-4917-a600-480bfdac5c9e
-- title:
--   Theorem 6.4 — every one-way protocol for $\mathrm{DDP}_{n,d}$ needs $c\ge\kappa\sum_{j\le\min(d,t)}\binom tj$ bits
-- statement:
--   Let $n\ge22$ and $1\le d\le n$, and let Alice's polynomial $q$ be uniform on $V_{n,d}$ and Bob's direction $a$ uniform on $\mathbb F_2^n\setminus\{0\}$, independently. Write $t=\lfloor n/2\rfloor-4$ and
--
--   $$
--   \kappa=\frac5{41}\Big(1-H_2\Big(\frac{11}{18}\Big)\Big),\qquad H_2(p)=-p\log_2p-(1-p)\log_2(1-p).
--   $$
--
--   Then every randomized one-way protocol for $\mathrm{DDP}_{n,d}$ with $c$-bit messages and average success probability at least $2/3$ satisfies
--
--   $$
--   c\ \ge\ \kappa\sum_{j=1}^{\min\{d,t\}}\binom tj .
--   $$
--
--   Moreover $\kappa>0$, and numerically $\kappa\approx0.00438$ (stated as $|\kappa-0.00438|\le5\cdot10^{-6}$; $\kappa=0.0043806\ldots$).
--
--   For fixed $d$ this gives the $\Omega_d(n^d)$ lower bound of Theorem 6.2; for $d\ge t$ the sum is $2^t-1$ and the bound is $\Omega(2^{n/2})$.
--
--   **Formalization Note** $H_2$ is the published `WildeQIT.binaryEntropy` (base 2). $t$ is computed with natural-number division and subtraction; for $n\ge22$, $t\ge7$ and nothing is truncated.
--
--   Differences from the source:
--   - reading: Numerically, κ ≈ 0.00438 → |κ − 0.00438| ≤ 0.000005; reason: the printed value is κ rounded to three significant figures
--   - encoding: H₂, the binary entropy in bits → published WildeQIT.binaryEntropy; reason: the same function −p log₂ p − (1 − p) log₂(1 − p)
--   - encoding: t = ⌊n/2⌋ − 4 → n / 2 − 4 in ℕ; reason: for n ≥ 22 this is ⌊n/2⌋ − 4 ≥ 7
--   - encoding: randomized public-coin one-way protocol communicating c bits → OneWayProtocol: finite coin law, Alice's c-bit message Fin c → Bool per (coin, input), Bob's output per (coin, message, input); reason: the model of §2.1, p.14 and pp.45, 60 (a c-bit message takes at most 2^c values); private coins are subsumed by public coins
--   - encoding: Alice's and Bob's inputs independent and uniform → the uniform law on the product of the input sets (avgSucc); reason: independent uniform marginals are the uniform product law
-- source:
--   Anselm, Ding, Gilboa, Grewal, Optimal and Verifiable Quantum Advantages in Communication Complexity, arXiv:2610.05585 (held version, sha256 4564aef3…), Theorem 6.4, p.44

import Mathlib
import Definitions.Def_WildeQIT_binaryEntropy
import Definitions.Def_PelagicFF_Supplement_OneWayProtocol
import Definitions.Def_PelagicFF_Supplement_DDP

namespace PelagicFF.Supplement

/-- **Theorem 6.4 (Classical lower bound at every degree).** Anselm, Ding, Gilboa, Grewal, *Optimal
and Verifiable Quantum Advantages in Communication Complexity*, arXiv:2610.05585 (held version,
sha256 4564aef3…), Theorem 6.4, p.44:

"Let n ≥ 22 and 1 ≤ d ≤ n. Choose Alice's polynomial to be uniform on V_{n,d} and Bob's direction
to be uniform on F₂ⁿ \ {0}, independently of Alice's input. Then every randomized classical one-way
protocol for DDP_{n,d} with average success probability at least 2/3 and communication cost c
satisfies c ≥ κ ∑_{j=1}^{min{d,t}} (t choose j), t = ⌊n/2⌋ − 4, where κ = (5/41)(1 − H₂(11/18)) > 0.
Numerically, κ ≈ 0.00438."

The three clauses: the lower bound, `κ > 0`, and `|κ − 0.00438| ≤ 5·10⁻⁶` (the rounding claim;
`κ = 0.0043806…`).

**Formalization Note.** `H₂` is the published `WildeQIT.binaryEntropy` (base 2). `t = n/2 − 4` is
natural-number division and subtraction; for `n ≥ 22`, `t ≥ 7` and nothing is truncated. The
independent uniform laws on `q` and `a` are the uniform law on the product (`avgSucc`). -/
theorem theorem_6_4 :
    (∀ n ≥ 22, ∀ d : ℕ, 1 ≤ d → d ≤ n → ∀ c : ℕ,
      ∀ P : OneWayProtocol (Vnd n d) (Dir n) (DDPOut n) c,
        (2 : ℝ) / 3 ≤ P.avgSucc (DDP n d) →
        (5 / 41 : ℝ) * (1 - WildeQIT.binaryEntropy (11 / 18)) *
            ∑ j ∈ Finset.Icc 1 (min d (n / 2 - 4)), ((n / 2 - 4).choose j : ℝ) ≤ (c : ℝ)) ∧
    0 < (5 / 41 : ℝ) * (1 - WildeQIT.binaryEntropy (11 / 18)) ∧
    |(5 / 41 : ℝ) * (1 - WildeQIT.binaryEntropy (11 / 18)) - 0.00438| ≤ 0.000005 := by sorry

end PelagicFF.Supplement
