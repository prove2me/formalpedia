-- Prove2me | Theorems.Thm_WFMFG_Conv_lemma_4_5
-- name    : WFMFG.Conv.lemma_4_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T22:14:27.448984+00:00
-- url     : https://prove2.me/theorems/12ef68a0-a750-4aeb-a757-0e97c377f304
-- title:
--   Lemma 4.5, p. 23 — moment and deviation bounds (4.18)–(4.20) for $(S_\mu[i]/(N\mu[i]))^\ell - 1$, $S_\mu$ multinomial
-- statement:
--   Let $d \ge 1$ and, for a probability vector $\mu$ on $[\![d]\!]$ with all $\mu[i] > 0$ and $N \ge 1$, let $S_\mu \sim \mathcal M_{N,\mu}$ be multinomial. Write $\underline\mu = \min_{e} \mu[e]$.
--
--   1. **(4.18).** For every integer $\ell \ge 1$ there is $C$ such that for all such $\mu$, all $i, j \in [\![d]\!]$ and $N \ge 1$,
--   $$
--   \Big|\mathbf E\Big[\Big(\tfrac{S_\mu[i]}{N\mu[i]}\Big)^\ell - 1\Big]\Big| \le \frac{\ell(\ell-1)}{2N\mu[i]} + C\sum_{k=3}^{\ell}\frac{1}{N^{k/2}\mu[i]^{k-1}},
--   \qquad
--   \Big|\mathbf E\Big[\tfrac{S_\mu[j]}{N\mu[j]}\Big\{\Big(\tfrac{S_\mu[i]}{N\mu[i]}\Big)^\ell - 1\Big\}\Big]\Big| \le \frac{\ell(\ell+1)}{2N\underline\mu} + C\sum_{k=3}^{\ell+1}\frac{1}{N^{k/2}\underline\mu^{k-1}},
--   $$
--   with $\sum_{k=3}^{2} = 0$.
--   2. **(4.19).** For every $\ell \ge 1$ and $p \ge 2$ there is $C$ such that for all such $\mu$, $i$ and $N \ge 1$ with $N\mu[i] \ge 1$,
--   $$
--   \mathbf E\Big[\Big|\Big(\tfrac{S_\mu[i]}{N\mu[i]}\Big)^\ell - 1\Big|^p\Big]^{1/p} \le C\sum_{k=1}^{\ell}(N\mu[i])^{-k/2}.
--   $$
--   3. **(4.20).** For every $\ell \ge 1$ and $\eta > 0$ there are $C$ and $c > 0$ such that for all such $\mu$, $i$ and $N \ge 1$,
--   $$
--   \mathbf P\Big(\Big|\Big(\tfrac{S_\mu[i]}{N\mu[i]}\Big)^\ell - 1\Big| \ge \eta\Big) \le C\exp\big(-cN\mu[i]^2\big).
--   $$
--
--   These estimates control the common-noise term of the Nash system, in which weights are multiplied by $S_\mu[i]/(N\mu[i])$; they are used in Lemma 4.8 and in the proof of Theorem 2.4.
--
--   **Formalization Note.** Expectations and probabilities are finite sums against the multinomial weights. The constants are uniform in $\mu$, as their use at a random $\mu$ in the proof of Theorem 2.4 requires. The second sum of (4.18) has a factor $C$ in Lean: the display on p. 23 omits it, but the proof on p. 45 includes it. In (4.19) the hypothesis $N\mu[i] \ge 1$ is added: without it the inequality fails (for $N = 1$, $\ell = p = 2$ the left side is of order $\mu[i]^{-3/2}$ and the right side of order $\mu[i]^{-1}$ as $\mu[i] \to 0$), and the last step of its proof (p. 45) uses it; the paper applies (4.19) where $N\min_e\mu[e] \ge 1$.
-- source:
--   Bayraktar, Cecchin, Cohen & Delarue, Finite State Mean Field Games with Wright–Fisher Common Noise as Limits of N-Player Weighted Games, arXiv:2012.04845v2, p. 23, Lemma 4.5, (4.18)–(4.20)

import Mathlib
import Definitions.Def_WFMFG_Conv_Simplex
import Definitions.Def_WFMFG_Conv_Multinomial
import Definitions.Def_WFMFG_Conv_Setting

open Finset

namespace WFMFG.Conv

theorem lemma_4_5 (d : ℕ) [NeZero d] :
    (∀ ℓ : ℕ, 1 ≤ ℓ → ∃ C : ℝ, ∀ μ ∈ stdSimplex ℝ (Fin d), (∀ i, 0 < μ i) →
      ∀ (i j : Fin d) (N : ℕ), 1 ≤ N →
        |multE N μ (fun k => ((k i : ℝ) / (N * μ i)) ^ ℓ - 1)| ≤
            (ℓ : ℝ) * (ℓ - 1) / (2 * N * μ i)
              + C * ∑ k ∈ Finset.Icc 3 ℓ, 1 / ((N : ℝ) ^ ((k : ℝ) / 2) * μ i ^ (k - 1)) ∧
        |multE N μ (fun k => ((k j : ℝ) / (N * μ j)) * (((k i : ℝ) / (N * μ i)) ^ ℓ - 1))| ≤
            (ℓ : ℝ) * (ℓ + 1) / (2 * N * univ.inf' univ_nonempty μ)
              + C * ∑ k ∈ Finset.Icc 3 (ℓ + 1),
                  1 / ((N : ℝ) ^ ((k : ℝ) / 2) * (univ.inf' univ_nonempty μ) ^ (k - 1))) ∧
    (∀ ℓ : ℕ, 1 ≤ ℓ → ∀ p : ℝ, 2 ≤ p → ∃ C : ℝ, ∀ μ ∈ stdSimplex ℝ (Fin d), (∀ i, 0 < μ i) →
      ∀ (i : Fin d) (N : ℕ), 1 ≤ N → 1 ≤ (N : ℝ) * μ i →
        (multE N μ (fun k => |((k i : ℝ) / (N * μ i)) ^ ℓ - 1| ^ p)) ^ (1 / p) ≤
          C * ∑ k ∈ Finset.Icc 1 ℓ, ((N : ℝ) * μ i) ^ (-(k : ℝ) / 2)) ∧
    (∀ ℓ : ℕ, 1 ≤ ℓ → ∀ η : ℝ, 0 < η → ∃ C c : ℝ, 0 < c ∧
      ∀ μ ∈ stdSimplex ℝ (Fin d), (∀ i, 0 < μ i) → ∀ (i : Fin d) (N : ℕ), 1 ≤ N →
        multE N μ (fun k => if η ≤ |((k i : ℝ) / (N * μ i)) ^ ℓ - 1| then 1 else 0) ≤
          C * Real.exp (-c * N * μ i ^ 2)) := by sorry

end WFMFG.Conv
