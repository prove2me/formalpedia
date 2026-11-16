-- Prove2me | Theorems.Thm_RLCDiscrepancy_Supplement_theorem_2_14
-- name    : RLCDiscrepancy.Supplement.theorem_2_14
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T03:53:32.44876+00:00
-- url     : https://prove2.me/theorems/5ff6cfbc-a8df-432b-8f18-94cfa4e59ae2
-- title:
--   Theorem 2.14 — above erasure list-recovery capacity, random linear codes are $(\zeta,\ell,\lceil(1+q^{-c\gamma n/(q^2\log(q/\gamma))})q^{\gamma n}\rceil)$-list-recoverable
-- statement:
--   There exist universal constants $c,c'>0$ such that the following holds. Let $n\in\mathbb N$, let $q$ be prime, $2\le\ell\le q-1$ and $\zeta\in(0,1)$. Let
--   $$
--   \beta=(1-\zeta)(1-\log_q\ell),\qquad 0<\gamma\le\tfrac12\min\{1-\beta,\beta\},\qquad R=\beta+\gamma,
--   $$
--   and assume $n\ge c'\,q^5\log^2(q/\gamma)/\gamma^2$. Let $C\subseteq\mathbb F_q^n$ be a random linear code of designed rate $R$. Then with probability at least $1-2q^{-c\gamma n/(q^2\log(q/\gamma))}$, both of the following hold:
--
--   1. $C$ is $(\zeta,\ell,L)$-list-recoverable with $L=\big\lceil(1+q^{-c\gamma n/(q^2\log(q/\gamma))})q^{\gamma n}\big\rceil$;
--   2. for every combinatorial rectangle $S=S_1\times\cdots\times S_n$ with $|S_i|=\ell$ for $(1-\zeta)n$ of the $i$'s and $|S_i|=q$ for the rest,
--   $$
--   |C\cap S|=\big(1\pm q^{-c\gamma n/(q^2\log(q/\gamma))}\big)\,|C|\Big(\frac{\ell}{q}\Big)^{(1-\zeta)n}.
--   $$
--
--   This is the erasure analogue of Theorem 2.12, at the erasure list-recovery capacity $(1-\zeta)(1-\log_q\ell)$.
--
--   **Formalization Note** The constants $c,c'$ are this theorem's own (existential, independent of those of Theorem 2.12). The exponent $(1-\zeta)n$ is real.
--
--   Differences from the source:
--   - encoding: q prime, F_q → a finite field F with Fintype.card F prime; reason: every field of prime order q is F_q
--   - encoding: unsubscripted log in log(q/γ) → Real.logb 2; reason: log(q/γ) occurs only as c/log(q/γ) and c′·log²(q/γ) with existential universal c, c′, so any fixed base gives an equivalent statement
--   - encoding: random linear code of designed rate R (k = Rn) → uniform G ∈ F^{n×k} with k : ℕ and (k : ℝ) = R·n, probability as the counting ratio over all G; reason: the paper's designed dimension k = Rn; no instance with Rn ∉ ℕ exists in the paper
--   - encoding: |X| = (1 ± ε)Y → (1 − ε)Y ≤ |X| ∧ |X| ≤ (1 + ε)Y; reason: the paper's notation for a two-sided bound
--   - reading: |S_i| = ℓ for (1−ζ)n of the i's, and |S_i| = q for the rest → every |S_i| ∈ {ℓ, q} and the number of i with |S_i| = ℓ equals the real (1−ζ)n; reason: the printed count; when (1−ζ)n is not an integer no rectangle qualifies, as printed (the appendix proof uses exactly ζn erasures)
-- source:
--   Doron, Leonov, Mosheiff, Navas, Resch, Ribeiro, Discrepancy for Random Linear Codes, arXiv:2606.24471 (PDF sha256 f03561c3…), Theorem 2.14, p.19; Eqs. (6)–(7), p.18

import Mathlib
import Definitions.Def_PunctSketch_coinProb
import Definitions.Def_RLCDiscrepancy_rlc
import Definitions.Def_RLCDiscrepancy_relDev
import Definitions.Def_RLCDiscrepancy_Supplement_IsErasureListRecoverable

universe u

namespace RLCDiscrepancy.Supplement

/-- **Theorem 2.14** (random linear codes achieve nearly optimal output list size in erasure
list-recovery above capacity). Doron, Leonov, Mosheiff, Navas, Resch, Ribeiro, *Discrepancy for Random Linear Codes*,
arXiv:2606.24471 (PDF sha256 f03561c3…), Theorem 2.14, p.19: "There exist universal constants c, c′ > 0
such that the following holds. Let n ∈ N, let q be prime, and let 2 ≤ ℓ ≤ q − 1 and ζ ∈ (0, 1). Let
β = (1 − ζ)(1 − log_q ℓ), 0 < γ ≤ (1/2) min{1 − β, β}, and set R = β + γ. Let C ⊆ F^n_q be a random
linear code of designed rate R. Then, assuming the lower bound on n given in Equation (6) above
holds, then the following events both hold, with the probability bound given in Equation (7).
1. The code C is (ζ, ℓ, L)-list-recoverable with L = ⌈(1 + q^{−cγn/(q² log(q/γ))}) q^{γn}⌉.
2. For every combinatorial rectangle S = S_1 × ⋯ × S_n with |S_i| = ℓ for (1 − ζ)n of the i's, and
|S_i| = q for the rest of them, we have |C ∩ S| = (1 ± q^{−cγn/(q² log(q/γ))}) |C| (ℓ/q)^{(1−ζ)n}."
Equations (6) and (7) (p.18): n ≥ c′ · q^5 log²(q/γ)/γ², and probability at least
1 − 2q^{−cγn/(q² log(q/γ))}.

**Formalization Note.** As in Theorem 2.12: universal `∃ c > 0, ∃ c' > 0` first (their own
constants, independent of those of Theorem 2.12), q = `Fintype.card F` prime, ℓ ≤ q − 1 as
`ℓ + 1 ≤ q`, log = `Real.logb 2` (base absorbed by c, c′), C = `rlc G` with G uniform and
`(k : ℝ) = R * n`, probability = `PunctSketch.coinProb`. In item 2, "|S_i| = ℓ for (1 − ζ)n of the
i's, and |S_i| = q for the rest" is: every |S_i| is ℓ or q, and the number of i with |S_i| = ℓ equals
the real number (1 − ζ)n (when (1 − ζ)n is not an integer no rectangle qualifies, as printed); the
exponent (1 − ζ)n is real (`Real.rpow`). -/
theorem theorem_2_14 :
    ∃ c : ℝ, 0 < c ∧ ∃ c' : ℝ, 0 < c' ∧
    ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F], (Fintype.card F).Prime →
    ∀ (n k ℓ : ℕ) (ζ β γ R : ℝ), 2 ≤ ℓ → ℓ + 1 ≤ Fintype.card F →
      0 < ζ → ζ < 1 →
      β = (1 - ζ) * (1 - Real.logb (Fintype.card F) ℓ) →
      0 < γ → γ ≤ (1 / 2) * min (1 - β) β →
      R = β + γ →
      c' * (Fintype.card F : ℝ) ^ 5 * Real.logb 2 ((Fintype.card F : ℝ) / γ) ^ 2 / γ ^ 2 ≤ n →
      (k : ℝ) = R * n →
      1 - 2 * (Fintype.card F : ℝ) ^ (-(c * γ * n /
            ((Fintype.card F : ℝ) ^ 2 * Real.logb 2 ((Fintype.card F : ℝ) / γ)))) ≤
        PunctSketch.coinProb (fun G : Matrix (Fin n) (Fin k) F =>
          IsErasureListRecoverable (codeFinset (rlc G)) ζ ℓ
            ⌈(1 + (Fintype.card F : ℝ) ^ (-(c * γ * n /
                ((Fintype.card F : ℝ) ^ 2 * Real.logb 2 ((Fintype.card F : ℝ) / γ)))))
              * (Fintype.card F : ℝ) ^ (γ * n)⌉₊ ∧
          ∀ S : Fin n → Finset F,
            (∀ i, (S i).card = ℓ ∨ (S i).card = Fintype.card F) →
            ((Finset.univ.filter (fun i => (S i).card = ℓ)).card : ℝ) = (1 - ζ) * n →
            (1 - (Fintype.card F : ℝ) ^ (-(c * γ * n /
                ((Fintype.card F : ℝ) ^ 2 * Real.logb 2 ((Fintype.card F : ℝ) / γ)))))
                * (codeFinset (rlc G)).card * ((ℓ : ℝ) / Fintype.card F) ^ ((1 - ζ) * n) ≤
              ((codeFinset (rlc G) ∩ Fintype.piFinset S).card : ℝ) ∧
            ((codeFinset (rlc G) ∩ Fintype.piFinset S).card : ℝ) ≤
              (1 + (Fintype.card F : ℝ) ^ (-(c * γ * n /
                ((Fintype.card F : ℝ) ^ 2 * Real.logb 2 ((Fintype.card F : ℝ) / γ)))))
                * (codeFinset (rlc G)).card * ((ℓ : ℝ) / Fintype.card F) ^ ((1 - ζ) * n)) := by sorry

end RLCDiscrepancy.Supplement
