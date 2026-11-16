-- Prove2me | Theorems.Thm_RLCDiscrepancy_Supplement_theorem_2_9
-- name    : RLCDiscrepancy.Supplement.theorem_2_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T03:51:34.01641+00:00
-- url     : https://prove2.me/theorems/e1927067-aa77-445c-8df9-c8f17816e65f
-- title:
--   Theorem 2.9 — above list-decoding capacity, every Hamming ball meets a random linear code in $(1\pm q^{-\gamma n/12})|C||B_\rho(0)|/q^n$ points
-- statement:
--   Let $\mathbb F_q$ be a finite field ($q$ any prime power), $n\in\mathbb N$, $0<\rho<1-1/q$, and $0<\gamma<\frac1n\log_q|B_\rho(0)|$ with $\gamma n\ge240\log_q n$. Set
--   $$
--   R=1-\frac1n\log_q|B_\rho(0)|+\gamma,
--   $$
--   and let $C\subseteq\mathbb F_q^n$ be a random linear code of designed rate $R$ (the image of a uniform $G\in\mathbb F_q^{n\times k}$, $k=Rn$). Then with probability at least
--   $$
--   1-4q^{1-\gamma n/3}-\frac{q^{-(1-R)n+1}}{(q-1)^2}-q^{2n-\gamma^2n^2/1440},
--   $$
--   both of the following hold:
--
--   1. for every $z\in\mathbb F_q^n$, $\;|B_\rho(z)\cap C|=\big(1\pm q^{-\gamma n/12}\big)\dfrac{|C|\,|B_\rho(0)|}{q^n}$;
--   2. $C$ is $(\rho,L)$-list-decodable with $L=\big\lceil(1+q^{-\gamma n/12})q^{\gamma n}\big\rceil$.
--
--   Above the list-decoding capacity, a random linear code therefore has the same list size as a uniformly random code, up to a $1+o(1)$ factor.
--
--   **Formalization Note** $|C|$ is the number of codewords of $C$ (not $q^k$); $\log_q$ is `Real.logb q`; real powers are `Real.rpow`; $L$ is the natural-number ceiling.
--
--   Differences from the source:
--   - encoding: random linear code of designed rate R (k = Rn) → uniform G ∈ F^{n×k} with k : ℕ and (k : ℝ) = R·n, probability as the counting ratio over all G; reason: the paper's designed dimension k = Rn; no instance with Rn ∉ ℕ exists in the paper
--   - encoding: |X| = (1 ± ε)Y → (1 − ε)Y ≤ |X| ∧ |X| ≤ (1 + ε)Y; reason: the paper's notation for a two-sided bound
-- source:
--   Doron, Leonov, Mosheiff, Navas, Resch, Ribeiro, Discrepancy for Random Linear Codes, arXiv:2606.24471 (PDF sha256 f03561c3…), Theorem 2.9, pp.16–17

import Mathlib
import Definitions.Def_PunctSketch_coinProb
import Definitions.Def_RLCDiscrepancy_rlc
import Definitions.Def_RLCDiscrepancy_relDev
import Definitions.Def_RLCDiscrepancy_Supplement_hammingBall
import Definitions.Def_RLCDiscrepancy_Supplement_IsListDecodable

namespace RLCDiscrepancy.Supplement

/-- **Theorem 2.9** (random linear codes achieve nearly optimal list size in list-decoding above
capacity). Doron, Leonov, Mosheiff, Navas, Resch, Ribeiro, *Discrepancy for Random Linear Codes*,
arXiv:2606.24471 (PDF sha256 f03561c3…), Theorem 2.9, pp.16–17: "Let n ∈ N, let q be a prime power, let 0 < ρ < 1 − 1/q, and
let 0 < γ < (1/n) log_q |B_ρ(0)|, where γn ≥ 240 log_q n. Set R := 1 − (1/n) log_q |B_ρ(0)| + γ. Let
C ⊆ F^n_q be a random linear code of designed rate R. Then, with probability at least
1 − 4q^{1−γn/3} − q^{−(1−R)n+1}/(q − 1)² − q^{2n−γ²n²/1440}, the following holds simultaneously for
every z ∈ F^n_q: |B_ρ(z) ∩ C| = (1 ± q^{−γn/12}) |C| · |B_ρ(0)|/q^n. (5) In particular, C is
(ρ, L)-list-decodable with L = ⌈(1 + q^{−γn/12}) q^{γn}⌉."

**Formalization Note.** F_q is a finite field `F` with q = `Fintype.card F` (any prime power). The
random linear code of designed rate R is `rlc G` for a uniformly random
`G : Matrix (Fin n) (Fin k) F` with `(k : ℝ) = R * n` (§2.1; no full-rank conditioning), and the
probability is the counting ratio `PunctSketch.coinProb` over all such G. |C| is the number of
vectors of the code (`codeFinset`), not q^k. "(1 ± ε)X" means (1 − ε)X ≤ · ≤ (1 + ε)X. The event is
the conjunction of (5) for every z and the list-decodability clause; L is the natural-number
ceiling `⌈·⌉₊` of a positive real. log_q is `Real.logb q`, real powers are `Real.rpow`. -/
theorem theorem_2_9 {F : Type*} [Field F] [Fintype F] [DecidableEq F] (n k : ℕ) (ρ γ R : ℝ)
    (hρ₀ : 0 < ρ) (hρ₁ : ρ < 1 - 1 / (Fintype.card F : ℝ))
    (hγ₀ : 0 < γ)
    (hγ₁ : γ < (1 / (n : ℝ)) * Real.logb (Fintype.card F)
      ((hammingBall ρ (0 : Fin n → F)).card : ℝ))
    (hγn : 240 * Real.logb (Fintype.card F) n ≤ γ * n)
    (hR : R = 1 - (1 / (n : ℝ)) * Real.logb (Fintype.card F)
      ((hammingBall ρ (0 : Fin n → F)).card : ℝ) + γ)
    (hk : (k : ℝ) = R * n) :
    1 - 4 * (Fintype.card F : ℝ) ^ (1 - γ * n / 3)
        - (Fintype.card F : ℝ) ^ (-(1 - R) * n + 1) / ((Fintype.card F : ℝ) - 1) ^ 2
        - (Fintype.card F : ℝ) ^ (2 * (n : ℝ) - γ ^ 2 * n ^ 2 / 1440) ≤
      PunctSketch.coinProb (fun G : Matrix (Fin n) (Fin k) F =>
        (∀ z : Fin n → F,
          (1 - (Fintype.card F : ℝ) ^ (-γ * n / 12)) * (codeFinset (rlc G)).card
              * (hammingBall ρ (0 : Fin n → F)).card / (Fintype.card F : ℝ) ^ n ≤
            ((hammingBall ρ z ∩ codeFinset (rlc G)).card : ℝ) ∧
          ((hammingBall ρ z ∩ codeFinset (rlc G)).card : ℝ) ≤
            (1 + (Fintype.card F : ℝ) ^ (-γ * n / 12)) * (codeFinset (rlc G)).card
              * (hammingBall ρ (0 : Fin n → F)).card / (Fintype.card F : ℝ) ^ n) ∧
        IsListDecodable (codeFinset (rlc G)) ρ
          ⌈(1 + (Fintype.card F : ℝ) ^ (-γ * n / 12)) * (Fintype.card F : ℝ) ^ (γ * n)⌉₊) := by sorry

end RLCDiscrepancy.Supplement
