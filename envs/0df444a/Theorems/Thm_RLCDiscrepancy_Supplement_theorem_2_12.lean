-- Prove2me | Theorems.Thm_RLCDiscrepancy_Supplement_theorem_2_12
-- name    : RLCDiscrepancy.Supplement.theorem_2_12
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T03:52:49.257799+00:00
-- url     : https://prove2.me/theorems/67026afe-1b28-4183-9e47-8397d94e669d
-- title:
--   Theorem 2.12 — above zero-error list-recovery capacity, random linear codes are $(\ell,\lceil(1+q^{-c\gamma n/(q^2\log(q/\gamma))})q^{\gamma n}\rceil)$-list-recoverable
-- statement:
--   There exist universal constants $c,c'>0$ such that the following holds. Let $n\in\mathbb N$, let $q$ be prime, $2\le\ell\le q-1$, and
--   $$
--   0<\gamma\le\tfrac12\min\{\log_q\ell,\ 1-\log_q\ell\},\qquad R=1-\log_q\ell+\gamma .
--   $$
--   Assume $n\ge c'\,q^5\log^2(q/\gamma)/\gamma^2$ (6). Let $C\subseteq\mathbb F_q^n$ be a random linear code of designed rate $R$. Then with probability at least $1-2q^{-c\gamma n/(q^2\log(q/\gamma))}$ (7), both of the following hold:
--
--   1. $C$ is $(\ell,L)$-list-recoverable with $L=\big\lceil(1+q^{-c\gamma n/(q^2\log(q/\gamma))})q^{\gamma n}\big\rceil$;
--   2. for every combinatorial rectangle $S=S_1\times\cdots\times S_n$ with $|S_i|=\ell$ for each $i$,
--   $$
--   |C\cap S|=\big(1\pm q^{-c\gamma n/(q^2\log(q/\gamma))}\big)\frac{|C|\,\ell^n}{q^n}.
--   $$
--
--   The constants $c,c'$ do not depend on $n,q,\ell,\gamma$. Above the zero-error list-recovery capacity $1-\log_q\ell$, random linear codes thus match the output list size of uniformly random codes.
--
--   **Formalization Note** $|C|$ is the number of codewords; the rectangle is `Fintype.piFinset S`; $L$ is the natural-number ceiling.
--
--   Differences from the source:
--   - encoding: q prime, F_q → a finite field F with Fintype.card F prime; reason: every field of prime order q is F_q
--   - encoding: unsubscripted log in log(q/γ) → Real.logb 2; reason: log(q/γ) occurs only as c/log(q/γ) and c′·log²(q/γ) with existential universal c, c′, so any fixed base gives an equivalent statement
--   - encoding: random linear code of designed rate R (k = Rn) → uniform G ∈ F^{n×k} with k : ℕ and (k : ℝ) = R·n, probability as the counting ratio over all G; reason: the paper's designed dimension k = Rn; no instance with Rn ∉ ℕ exists in the paper
--   - encoding: |X| = (1 ± ε)Y → (1 − ε)Y ≤ |X| ∧ |X| ≤ (1 + ε)Y; reason: the paper's notation for a two-sided bound
-- source:
--   Doron, Leonov, Mosheiff, Navas, Resch, Ribeiro, Discrepancy for Random Linear Codes, arXiv:2606.24471 (PDF sha256 f03561c3…), Theorem 2.12, Eqs. (6)–(7), p.18

import Mathlib
import Definitions.Def_PunctSketch_coinProb
import Definitions.Def_RLCDiscrepancy_rlc
import Definitions.Def_RLCDiscrepancy_relDev
import Definitions.Def_RLCDiscrepancy_Supplement_IsListRecoverable

universe u

namespace RLCDiscrepancy.Supplement

/-- **Theorem 2.12** (random linear codes achieve nearly optimal output list size in zero-error
list-recovery above capacity). Doron, Leonov, Mosheiff, Navas, Resch, Ribeiro, *Discrepancy for Random Linear Codes*,
arXiv:2606.24471 (PDF sha256 f03561c3…), Theorem 2.12, p.18: "There exist universal constants c, c′ > 0
such that the following holds. Let n ∈ N, let q be prime, and let 2 ≤ ℓ ≤ q − 1. Let
0 < γ ≤ (1/2) min{log_q ℓ, 1 − log_q ℓ}, and set R = 1 − log_q ℓ + γ. Assume that
n ≥ c′ · q^5 log²(q/γ)/γ². (6) Let C ⊆ F^n_q be a random linear code of designed rate R. Then, with
probability at least 1 − 2q^{−cγn/(q² log(q/γ))}, (7) the following events both hold: 1. the code C is
(ℓ, L)-list-recoverable with L = ⌈(1 + q^{−cγn/(q² log(q/γ))}) q^{γn}⌉. 2. For every combinatorial
rectangle S = S_1 × ⋯ × S_n with |S_i| = ℓ for each i, we have
|C ∩ S| = (1 ± q^{−cγn/(q² log(q/γ))}) |C|ℓ^n/q^n."

**Formalization Note.** The universal constants come first: `∃ c > 0, ∃ c' > 0`, then every prime
field. F_q is a finite field `F` whose cardinality q is prime (equivalently `ZMod q`). ℓ ≤ q − 1 is
`ℓ + 1 ≤ q`. The unsubscripted log is `Real.logb 2`; its base only rescales c and c′, which are
existential. The random linear code of designed rate R is `rlc G` for a uniform
`G : Matrix (Fin n) (Fin k) F` with `(k : ℝ) = R * n`; the probability is the counting ratio
`PunctSketch.coinProb`. |C| is the number of codewords; the rectangle is `Fintype.piFinset S`; L is the
natural-number ceiling of a real; "(1 ± ε)X" is (1 − ε)X ≤ · ≤ (1 + ε)X. -/
theorem theorem_2_12 :
    ∃ c : ℝ, 0 < c ∧ ∃ c' : ℝ, 0 < c' ∧
    ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F], (Fintype.card F).Prime →
    ∀ (n k ℓ : ℕ) (γ R : ℝ), 2 ≤ ℓ → ℓ + 1 ≤ Fintype.card F →
      0 < γ →
      γ ≤ (1 / 2) * min (Real.logb (Fintype.card F) ℓ) (1 - Real.logb (Fintype.card F) ℓ) →
      R = 1 - Real.logb (Fintype.card F) ℓ + γ →
      c' * (Fintype.card F : ℝ) ^ 5 * Real.logb 2 ((Fintype.card F : ℝ) / γ) ^ 2 / γ ^ 2 ≤ n →
      (k : ℝ) = R * n →
      1 - 2 * (Fintype.card F : ℝ) ^ (-(c * γ * n /
            ((Fintype.card F : ℝ) ^ 2 * Real.logb 2 ((Fintype.card F : ℝ) / γ)))) ≤
        PunctSketch.coinProb (fun G : Matrix (Fin n) (Fin k) F =>
          IsListRecoverable (codeFinset (rlc G)) ℓ
            ⌈(1 + (Fintype.card F : ℝ) ^ (-(c * γ * n /
                ((Fintype.card F : ℝ) ^ 2 * Real.logb 2 ((Fintype.card F : ℝ) / γ)))))
              * (Fintype.card F : ℝ) ^ (γ * n)⌉₊ ∧
          ∀ S : Fin n → Finset F, (∀ i, (S i).card = ℓ) →
            (1 - (Fintype.card F : ℝ) ^ (-(c * γ * n /
                ((Fintype.card F : ℝ) ^ 2 * Real.logb 2 ((Fintype.card F : ℝ) / γ)))))
                * (codeFinset (rlc G)).card * (ℓ : ℝ) ^ n / (Fintype.card F : ℝ) ^ n ≤
              ((codeFinset (rlc G) ∩ Fintype.piFinset S).card : ℝ) ∧
            ((codeFinset (rlc G) ∩ Fintype.piFinset S).card : ℝ) ≤
              (1 + (Fintype.card F : ℝ) ^ (-(c * γ * n /
                ((Fintype.card F : ℝ) ^ 2 * Real.logb 2 ((Fintype.card F : ℝ) / γ)))))
                * (codeFinset (rlc G)).card * (ℓ : ℝ) ^ n / (Fintype.card F : ℝ) ^ n) := by sorry

end RLCDiscrepancy.Supplement
