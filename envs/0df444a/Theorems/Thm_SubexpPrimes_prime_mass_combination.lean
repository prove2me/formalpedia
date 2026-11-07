-- Prove2me | Theorems.Thm_SubexpPrimes_prime_mass_combination
-- name    : SubexpPrimes.prime_mass_combination
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:02:21.73143+00:00
-- url     : https://prove2.me/theorems/39665dd6-8344-4406-a8b4-e195c6479f63
-- title:
--   Proof of Proposition 6.1 — $W_C$ is within $2^{-\rho-2}$ of a combination of contractions at scale $n+\rho$
-- statement:
--   Let $C$ be admissible, $n\ge2$, $\rho\ge0$. With $Q=n+\rho+3\lceil\log n\rceil+15$ and $P=n+2Q+4$, there are $n$ networks $G_1,\dots,G_n$, with coefficients $b_e=\mu(e)$ and normalizations $a_e=-P$, forming a combination of contractions at scale $s=n+\rho$, such that $S=\sum_e\mu(e)2^{-P}Z(G_e)$ satisfies
--
--   $$
--   |S-W_C|\le2^{-\rho-2}.
--   $$
--
--   The proof of Theorem 1 cites this statement at $\rho=2$, where the error $2^{-4}$ is below $(\ln 2)/8$.
--
--   **Formalization Note** The networks are padded to $\Theta(s)$ edges and to degree at most $m^{3/4}$, as the hypotheses of Theorem 2.5 require.
--
--   Differences from the source:
--   - reading: there is a network → an explicit family: one builder machine, one entry machine, one constant, all polynomial; reason: Definition 2.3 and p.28 ("the arithmetic parts are explicit, and the rotation constants take time poly(p)") claim it, and Theorem 2.5 evaluates only such networks; this is the stronger reading and it implies the bare existence
--   - encoding: every O(·) and poly(·) → explicit expressions with one constant, quantified before the instance; reason: the constants may depend only on the data fixed before the instance
--   - reading: constructed in time poly(s + L), with L the length of C → L read as the length of the index word (1ⁿ, 1^ρ, d); reason: the two are polynomially related, since that word has length n + ρ + L + O(1)
--   - encoding: C admissible: constructed, and its entries computed, in time poly(n + L) → builder and entry machine of the admissible family bounded in time and space by one polynomial; reason: in the PrimitiveMachine model the visited space is at most the input length plus the number of tapes times (time + 1), and the inputs here have length polynomial in the same quantity, so a time bound gives the space bound with a larger constant; the constant is universally quantified, so no instance is lost
-- source:
--   Gajulapalli, Deterministic Construction of Primes in Subexponential Time (manuscript, sha256 6ad4d3de…), proof of Proposition 6.1, p.28

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_SubexpPrimes_Admissible
import Definitions.Def_SubexpPrimes_primeMass
import Definitions.Def_SubexpPrimes_CombTerm

set_option autoImplicit false

namespace SubexpPrimes

open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.Computation
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

open scoped ArithmeticFunction.Moebius in
/-- **`W_C` is within a combination of contractions** — Gajulapalli, *Deterministic Construction of Primes in Subexponential Time*
(manuscript, sha256 6ad4d3de…), proof of Proposition 6.1, p.28.

With `Q = n + ρ + 3⌈log n⌉ + 15` and `P = n + 2Q + 4`: there are `h = n` networks with coefficients
`b_e = µ(e)` and normalizations `a_e = -P` such that `S = ∑_e µ(e) 2^{-P} Z(G_e)` satisfies
`|S - W_C| ≤ 2^{-ρ-2}`; "in other words, `W_C` is within `2^{-ρ-2}` of a combination of contractions
at scale `s = n + ρ`". Theorem 1's proof cites this at `ρ = 2`.

**Formalization Note.** Padding the networks to `Θ(s)` edges and maximum degree at most `m^{3/4}` is
included in `CombinationFamily`, which requires the hypotheses of Theorem 2.5 for every network. -/
theorem prime_mass_combination {δ : Type} (encD : δ → List Bool) (C : ℕ → δ → List Bool → Prop)
    (hC : Admissible encD C) :
    ∃ (ts : ℕ × ℕ × δ → List CombTerm) (T : (D : NetDesc) → D.Tables ℚ),
      CombinationFamily
        (fun a => Encoding.encodeList id [List.replicate a.1 true, List.replicate a.2.1 true,
          encD a.2.2])
        (fun a => 2 ≤ a.1) (fun a => a.1 + a.2.1) ts T ∧
      ∀ (n ρ : ℕ) (d : δ), 2 ≤ n →
        let Q := n + ρ + 3 * Nat.clog 2 n + 15
        let P := n + 2 * Q + 4
        (ts (n, ρ, d)).length = n ∧
        (∀ e ∈ Finset.Icc 1 n, ∃ t, (ts (n, ρ, d))[e - 1]? = some t ∧
          t.b = μ e ∧ t.a = -(P : ℤ)) ∧
        |primeMass n (C n d) - combValue T (ts (n, ρ, d))| ≤ (2 : ℝ) ^ (-((ρ : ℤ) + 2)) := by sorry

end SubexpPrimes
