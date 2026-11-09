-- Prove2me | Theorems.Thm_TriFormQ_theorem_5
-- name    : TriFormQ.theorem_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T21:47:43.510445+00:00
-- url     : https://prove2.me/theorems/eb1a3337-1638-4e49-bb14-c54aa4c75e92
-- title:
--   Theorem 5 (weighted-list identification): per-matrix cost $O_q(\sqrt{\log(1/p_\mu(M))}+\ell\lambda(\ell/\varepsilon))$ (corrected: $\ell=\max\{1,\log\log L\}$)
-- statement:
--   Let $\mathbb F_q$ be a finite field. There is a constant $C$ (depending only on $q$) such that the following holds for every $n$, $L$, every explicitly given list $M^1,\dots,M^L$ of $n\times n$ matrices over $\mathbb F_q$, every probability distribution $\mu=(\mu_1,\dots,\mu_L)$ on $[L]$ and every $\varepsilon>0$. Let
--
--   $$p_\mu(M^i)=\sum_{j:\ M^j=M^i}\mu_j,\qquad \ell=\max\{1,\log_2\log_2L\},\qquad K=\ell\cdot\max\{1,\log_2(\ell/\varepsilon)\}.$$
--
--   There is a randomized quantum query algorithm, depending on the list, $\mu$ and $\varepsilon$ only, such that, with the evaluation oracle of $x^\top M^iy$:
--
--   1. for every $i$, it outputs an index $j$ with $M^j=M^i$ with probability at least $1-\varepsilon$, and, if $p_\mu(M^i)>0$, every run makes at most
--   $$C\Big(\sqrt{\log_2\big(1/p_\mu(M^i)\big)}+K\Big)$$
--   queries;
--   2. the $\mu$-average of these worst-case counts satisfies
--   $$\sum_{i=1}^L\mu_i\,\mathrm{maxQueries}(M^i)\ \le\ C\Big(\sum_{i=1}^L\mu_i\sqrt{\log_2(1/\mu_i)}+K\Big).$$
--
--   Heavily weighted matrices are thus identified with few queries; in the main algorithm the weights are chosen so that the algorithm acts as a sieve on the list of trilinear forms.
--
--   Differences from the source:
--   - correction: $\log\log L\cdot\log\frac{\log\log L}{\varepsilon}$ → $\ell\cdot\max\{1,\log_2(\ell/\varepsilon)\}$ with $\ell=\max\{1,\log_2\log_2L\}$; reason: the printed term is undefined at $L=1$, zero at $L=2$, and negative for $\varepsilon>\log\log L$ (e.g. $L=16$, $\mu$ a point mass, $\varepsilon=4$), which no query count meets
--   - reading: $p_\mu(M)$, the probability assigned to matrix $M$ by $\mu$ → the total mass $\mu$ puts on the indices whose matrix equals $M$; reason: the list may repeat; this is the probability that the oracle matrix is $M$, and the larger value gives the smaller bound
--   - reading: query bound $O_q(\sqrt{\log(1/p_\mu(M))}+\dots)$ for every $M$ → the count clause is required when $p_\mu(M^i)>0$; correctness for every $i$; reason: for $p_\mu(M)=0$ the printed bound is $+\infty$
--   - reading: correctly identifies $M$ with probability at least $1-\varepsilon$ using at most $X$ queries → success probability at least $1-\varepsilon$, and every positive-probability run on $M^i$ makes at most $X$ queries; reason: the stronger of the two readings (the other: the event "correct within $X$ queries" has probability $\ge1-\varepsilon$, which is what the printed proof shows); see the moderation notes
--   - reading: Consequently, with $\varepsilon$ constant and lower-order terms ignored, the expected number of queries is $O_q(\sum_ip_i\sqrt{\log(1/p_i)})$ → clause 2, the $\mu$-average of the per-matrix worst-case counts bounded by $C(\sum_i\mu_i\sqrt{\log_2(1/\mu_i)}+K)$; reason: the sentence's statement with $\varepsilon$ arbitrary and the lower-order term kept explicitly
--   - encoding: randomized quantum query algorithm making at most $X$ queries → an `AdaptiveAlg` (rounds of the platform's `QueryAlg` against the standard oracle, full measurement, classical choice of the next round) chosen before the oracle, whose worst-case query count over positive-probability runs on that oracle is at most $X$; reason: platform query model; classical coins are 0-query rounds and offline computation on explicit data is free, as in the paper
-- source:
--   Grigorescu–Juba–Wimmer–Xie, Optimal Quantum Query Bounds for Identifying Classes of 3-Tensors, STOC 2027 submission (manuscript sha256 c56b0365…), Theorem 5 (Weighted-list identification), p.20 (PDF p.23)

import Definitions.Def_TriFormQ_bilOracle
import Definitions.Def_TriFormQ_AdaptiveAlg_outProb
import Definitions.Def_TriFormQ_AdaptiveAlg_maxQueries

namespace TriFormQ

/-- Grigorescu–Juba–Wimmer–Xie, *Optimal Quantum Query Bounds for Identifying Classes of
3-Tensors*, STOC 2027 submission (manuscript sha256 c56b0365…), Theorem 5 (Weighted-list
identification), p.20 (PDF p.23): "Let M = {M¹, …, M^L} be a list of L explicitly given bilinear
forms on an n-dimensional vector space over 𝔽_q. Let µ = (pᵢ)_{i∈[L]} be a distribution on [L]
giving the probability that Mⁱ ∈ M is selected as the oracle matrix with query access. Then, for
every ε > 0, there is a randomized quantum query algorithm that, for every M ∈ M, if M is chosen
as the secret matrix oracle, the algorithm correctly identifies M with probability at least
1 − ε using at most O_q(√(log(1/p_µ(M))) + log log L · log(log log L / ε)) quantum oracle
queries, where p_µ(M) is the probability assigned to matrix M by µ. Consequently, if we assume
that ε is a constant and ignore the lower order terms, then the expected number of quantum
queries is O_q(Σᵢ pᵢ √(log(1/pᵢ)))."

**Formalization Note.** One constant `C` depending only on the field, before `n`, `L`, the list,
`µ` and `ε`; the algorithm depends on the list, `µ` and `ε`, not on the oracle. `p_µ(M)` is the
total mass `µ` puts on indices whose matrix is `M` (the list may repeat). With
`ℓ = max{1, log₂ log₂ L}` and `K = ℓ · max{1, log₂(ℓ/ε)}`: (i) for every `i`, on oracle `Mⁱ` the
algorithm outputs an index of `Mⁱ` with probability `≥ 1 − ε`, and if `p_µ(Mⁱ) > 0` every run of
positive probability makes at most `C(√(log₂(1/p_µ(Mⁱ))) + K)` queries; (ii) the µ-average of
these worst-case counts is at most `C(Σᵢ µᵢ √(log₂(1/µᵢ)) + K)` (the "Consequently" sentence,
with the lower-order term kept). -/
theorem theorem_5 {F : Type} [Field F] [Fintype F] [DecidableEq F] :
    ∃ C : ℝ, ∀ (n L : ℕ) (Ms : Fin L → Matrix (Fin n) (Fin n) F) (μ : Fin L → ℝ),
      (∀ i, 0 ≤ μ i) → ∑ i, μ i = 1 → ∀ ε : ℝ, 0 < ε →
      ∃ A : AdaptiveAlg (Vec F n × Vec F n) F (Option (Fin L)),
        (∀ i : Fin L,
          1 - ε ≤ A.outProb (bilOracle (Ms i)) (fun o => ∃ j, o = some j ∧ Ms j = Ms i) ∧
          (0 < ∑ j ∈ Finset.univ.filter (fun j => Ms j = Ms i), μ j →
            (A.maxQueries (bilOracle (Ms i)) : ℝ) ≤
              C * (Real.sqrt (Real.logb 2 (1 / ∑ j ∈ Finset.univ.filter (fun j => Ms j = Ms i), μ j)) +
                max 1 (Real.logb 2 (Real.logb 2 L)) *
                  max 1 (Real.logb 2 (max 1 (Real.logb 2 (Real.logb 2 L)) / ε))))) ∧
        ∑ i, μ i * (A.maxQueries (bilOracle (Ms i)) : ℝ) ≤
          C * (∑ i, μ i * Real.sqrt (Real.logb 2 (1 / μ i)) +
            max 1 (Real.logb 2 (Real.logb 2 L)) *
              max 1 (Real.logb 2 (max 1 (Real.logb 2 (Real.logb 2 L)) / ε))) := by sorry

end TriFormQ
