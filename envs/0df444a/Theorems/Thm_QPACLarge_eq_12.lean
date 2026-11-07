-- Prove2me | Theorems.Thm_QPACLarge_eq_12
-- name    : QPACLarge.eq_12
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:07:05.452446+00:00
-- url     : https://prove2.me/theorems/f7e23b74-5dd8-46e0-91e0-eae4dcd80d67
-- title:
--   Eq. (12) — query-bounded learners succeed at advantage $\theta_n/r_n$ with average probability $\le1/(16r_n)$
-- statement:
--   Let $\lambda_n > 0$, and let $s : \mathbb N \to \mathbb N$ satisfy $2^{-s(n)} \le \lambda_n \le 4 \cdot 2^{-s(n)}$ for all large $n$ (Eq. (9)). Assume $\lambda_n 2^{n/2} = n^{\omega(1)}$ and $\lambda_n = n^{-\omega(1)}$. Fix an integer $k \ge 1$, let $r_n, \theta_n, m_n, M_n$ be as in Eq. (11), and let $B$ be a randomized classical learner with polynomial query bound $q(n)$. Then for all large $n$,
--
--   $$
--   \mathbb E_{g \sim \mathrm{ALL}_{m_n}}\Big[\Pr_B\Big[\Pr_{x,z}[h(x,z) = g(x)] \ge \frac12 + \frac{\theta_n}{r_n}\Big]\Big] \le \frac{r_n^2}{M_n\theta_n^2} = \frac{1}{16 r_n}, \tag{12}
--   $$
--
--   where the targets are the padded functions $f_g$ with core length $m_n$. Since $\theta_n/r_n \le \lambda_n/n^k$ and $1/(16 r_n) \le 1/n^k$, this gives the unconditional classical bullet of Theorem 1.5, and the gap below $1/n^k$ is what the conditional bullet needs.
--
--   Differences from the source:
--   - generalization: a classical polynomial-time learner $B$ with polynomial query bound $q(n)$ → any family of randomized decision trees with at most $q(n)$ queries at length $n$ ($q$ a polynomial) and arbitrary hypotheses; reason: a polynomial-time learner with fixed coins is such a tree; the argument uses only the query bound
--   - generalization: $s(n)$ output by the polynomial-time algorithm of Eq. (9) → any $s : \mathbb N \to \mathbb N$ with Eq. (9) eventually; reason: the derivation uses only Eq. (9); every constructive $s$ is such an $s$
--   - reading: $\lambda_n 2^{n/2} = n^{\omega(1)}$, $\lambda_n = n^{-\omega(1)}$, $g = \omega(\log n)$ → for every $c \in \mathbb N$, eventually $n^c 2^{-n/2} \le \lambda_n$, $\lambda_n \le n^{-c}$, $c\log n \le g(n)$; reason: the standard meaning of $\omega(\cdot)$
--   - encoding: $\lceil\log_2 n\rceil$ → `Nat.clog 2 n`; reason: equal for every $n \ge 1$
-- source:
--   Oliveira, Unconditional Quantum PAC Learning Advantage in the Large Error Regime, arXiv:2610.23268 (held file sha256 e749e7c9…), Section 5.2, p.36, Eq. (12)

import Mathlib
import Definitions.Def_QPACLarge_treeSuccess
import Definitions.Def_QPACLarge_padFn
import Definitions.Def_QPACLarge_agreement
import Definitions.Def_QPACLarge_rN
import Definitions.Def_QPACLarge_mN

namespace QPACLarge

open QAlgorithms Filter

/-- **Eq. (12): average success `≤ 1/(16rₙ)` at advantage `θₙ/rₙ`.**
Oliveira, *Unconditional Quantum PAC Learning Advantage in the Large Error Regime*, arXiv:2610.23268 (held file sha256 e749e7c9…), Section 5.2, p.36: "Classical Lower Bound. Fix a classical polynomial time learner `B`, with
polynomial query bound `q(n)`. By Equation (11), `q(n) ≤ Mₙθₙ/rₙ` eventually. Apply Lemma 5.1 at
advantage `θₙ/rₙ` to obtain `E_{g∼ALL_{mₙ}}[Pr_B[Pr_{x,z}[h(x, z) = g(x)] ≥ 1/2 + θₙ/rₙ]] ≤
rₙ²/(Mₙθₙ²) = 1/(16rₙ)`. (12)"

With `θₙ = 2^{−s(n)}`, `mₙ = 2s(n) + 3k⌈log₂ n⌉ + 4` (`mN`), `Mₙ = 2^{mₙ}`, `rₙ = 2^{k⌈log₂ n⌉}` (`rN`),
`f_g` the padded function of Lemma 5.1.

**Formalization Note.** The learner is any family of randomized decision trees with at most `q(n)`
queries at length `n` (`q` a polynomial) and arbitrary hypotheses. `k` is a positive integer
(p.33); `λ`, `s` satisfy the hypotheses of Eq. (10), read as in `eq_10`. -/
theorem eq_12 (k : ℕ) (hk : 1 ≤ k) (lam : ℕ → ℝ) (s : ℕ → ℕ) (hpos : ∀ n, 0 < lam n)
    (h9 : ∀ᶠ n : ℕ in atTop, ((2 : ℝ) ^ s n)⁻¹ ≤ lam n ∧ lam n ≤ 4 * ((2 : ℝ) ^ s n)⁻¹)
    (hlow : ∀ c : ℕ, ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ c * (2 : ℝ) ^ (-(n : ℝ) / 2) ≤ lam n)
    (hup : ∀ c : ℕ, ∀ᶠ n : ℕ in atTop, lam n ≤ (n : ℝ) ^ (-(c : ℝ)))
    (q : Polynomial ℕ) (R : (n : ℕ) → RandDecisionTree (Qubits n) Bool (Qubits n → Bool))
    (hR : ∀ n, RandMakesAtMost (R n) (q.eval n)) :
    ∀ᶠ n : ℕ in atTop,
      ((2 : ℝ) ^ (2 ^ mN k n (s n)))⁻¹ * ∑ g : Qubits (mN k n (s n)) → Bool,
          treeSuccess (R n) (padFn n g)
            (fun h => 1 / 2 + ((2 : ℝ) ^ s n)⁻¹ / rN k n ≤ agreement (padFn n g) h) ≤
        1 / (16 * (rN k n : ℝ)) := by sorry

end QPACLarge
