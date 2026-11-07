-- Prove2me | Theorems.Thm_StretchDepth_lemma_1
-- name    : StretchDepth.lemma_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:07:25.80281+00:00
-- url     : https://prove2.me/theorems/a194405d-a360-42d9-9b59-888e7f3deaef
-- title:
--   Lemma 1 (corrected: $O(1+\log qd)$ for $O(\log qd)$) — the key lemma on reachable outputs
-- statement:
--   There is a universal constant $C>0$ such that the following holds. Let $H^{(\cdot)}:\{0,1\}^m\to\{0,1\}^M$ be a $(q,d)$-construction from an oracle $G:\{0,1\}^n\to\{0,1\}^N$ with $N>n$ and $q,d\ge1$. Let $1\le s<2^n/q$ and $p=s/2^n$. Then
--   $$
--   \Pr_{\rho\sim\mathcal R^{n,N}_p,\,y\sim U_M}\bigl[\exists G\supseteq\rho,\ y\in\mathrm{range}(H^G)\bigr]\le(q+1)\bigl(d(q+1)^2+1\bigr)\,2^{m-M\left(\frac{n-\log_2 qs}{N}\right)^d}.
--   $$
--   Moreover, for every real $\lambda$, this probability is at most $2^{-\lambda}$ provided
--   $$
--   M\ge\bigl(m+C(1+\log_2 qd)+\lambda\bigr)\Bigl(\frac{N}{n-\log_2 qs}\Bigr)^d.
--   $$
--   This is the key lemma of the paper: after a random restriction, the outputs reachable by a low-depth construction are a small fraction of $\{0,1\}^M$.
--
--   **Formalization Note** There is no no-repeat hypothesis here: it holds for every $(q,d)$-construction.
--
--   Differences from the source:
--   - correction: O(log qd) in the "in particular" clause → C(1 + log_2 qd); reason: the printed clause is false at q = d = 1 since log qd = 0: n = 2, N = 3, m = 0, M = 3, s = 1, lambda = 2, H^G() = G(00) meets the hypothesis 3 >= 2(3/2), and the probability is 1/4 + (3/4)(1/8) = 11/32 > 1/4; the two forms agree for qd >= 2
--   - generalization: poly(qd) → the explicit (q+1)(d(q+1)^2+1); reason: the value the proof yields, at most 10(qd)^3 for q, d >= 1
-- source:
--   Korten, Tight Depth Lower Bounds for Stretch Amplification, STOC 2027 submission (manuscript sha256 32d209e2…), Lemma 1, p.16

import Definitions.Def_StretchDepth_IsConstruction
import Definitions.Def_StretchDepth_testOf
import Definitions.Def_StretchDepth_crit

namespace StretchDepth

/-- **Lemma 1 (corrected: `O(1 + log qd)` in place of `O(log qd)`).**
Korten, *Tight Depth Lower Bounds for Stretch Amplification*, STOC 2027 submission (manuscript
sha256 32d209e2…), Lemma 1, p.16: "Let H(·) : {0, 1}m → {0, 1}M be a (q, d) construction from an oracle
G : {0, 1}n → {0, 1}N, N > n, q, d ≥ 1. Let 1 ≤ s < 2n/q be any parameter and let p = s/2n. Then
Pr_{ρ∼Rn,N p, y∼UM}[∃G ⊇ ρ, y ∈ range(HG)] ≤ poly(qd) · 2^{m−M((n−log qs)/N)^d}. In particular, the
probability on the left-hand-side of the above inequality is at most 2−λ provided
M ≥ (m + O(log qd) + λ)(N/(n−log qs))^d."

**Formalization Note.** `poly(qd)` is the explicit `(q+1)(d(q+1)²+1)` of the proof. The constant of
`O(·)` is universal, so `C` comes before the instance. The printed `O(log qd)` is `0` at
`q = d = 1`, where the clause is false: `n = 2`, `N = 3`, `m = 0`, `M = 3`, `s = 1`, `λ = 2`,
`H^G() = G(00)` meets the printed hypothesis `3 ≥ 2 · (3/2)`, and the probability is
`1/4 + (3/4)(1/8) = 11/32 > 1/4`. So the clause uses `O(1 + log qd)`, which is the same for
`qd ≥ 2`. No `NoRepeat` hypothesis: Lemma 1 holds for every `(q, d)`-construction. -/
theorem lemma_1 :
    ∃ C : ℝ, 0 < C ∧ ∀ (n N m M q d : ℕ) (s : ℝ) (H : Bits m → RoundTree n N M),
      n < N → 1 ≤ q → 1 ≤ d → 1 ≤ s → (q : ℝ) * s < 2 ^ n → IsConstruction H q d →
      rangeProb (s / 2 ^ n) H ≤
          ((q : ℝ) + 1) * ((d : ℝ) * ((q : ℝ) + 1) ^ 2 + 1) *
            (2 : ℝ) ^ ((m : ℝ) - M * (ell n q s / N) ^ d) ∧
        ∀ lam : ℝ,
          ((m : ℝ) + C * (1 + Real.logb 2 ((q : ℝ) * d)) + lam) * ((N : ℝ) / ell n q s) ^ d ≤ M →
          rangeProb (s / 2 ^ n) H ≤ (2 : ℝ) ^ (-lam) := by sorry

end StretchDepth
