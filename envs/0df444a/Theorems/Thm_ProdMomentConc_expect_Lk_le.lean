-- Prove2me | Theorems.Thm_ProdMomentConc_expect_Lk_le
-- name    : ProdMomentConc.expect_Lk_le
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T09:13:58.144831+00:00
-- url     : https://prove2.me/theorems/078d524f-e5ce-4719-b489-2f5c2ede2fb3
-- title:
--   §A.2 — the expectation bound $\mathbb E L_k \le d_R k$
-- statement:
--   Let $P_1,\dots,P_n \subseteq [m]$ be the read sets of the dependency graph, $d_R = \frac1n\sum_i |P_i|$ its average right degree, $k \le n$, and $I$ a uniformly random $k$-subset of $[n]$. Then
--
--   $$
--   \mathbb E L_k \le d_R k,
--   $$
--
--   where $L_k$ is the number of underlying variables read by the outputs in $I$.
--
--   The bound holds because $L_k \le \sum_{i \in I} |P_i|$ and each output lies in $I$ with probability $k/n$. It turns the tail estimates of $L_k$ around $\mathbb E L_k$ into the condition $r > d_R k$ of Lemma A.2 (ii) and Theorem 3.5.
--
--   **Formalization Note** $L_k$ is `Lk P I` with $I \sim$ `kSubsetLaw n k`, and $d_R$ is `dR P`.
--
--   Differences from the source:
--   - generalization: k a positive integer in the setting of Theorem 3.5 → any k ≤ n and any read sets; reason: the source's case is an instance
-- source:
--   Saks, Srinivasan, Valieva, Concentration from Product Moments via an Additional Element of Randomness, arXiv:2608.04125 (held version, sha256 5218e9d0405f975413d3e2dd2c4c9d6b43c772029e645965afee1cd619ae38aa), §A.2, p.36 (PDF p.36)

import Mathlib
import Definitions.Def_ProdMomentConc_edgeCount
import Definitions.Def_ProdMomentConc_kSubsetLaw
import Definitions.Def_ProdMomentConc_Lk

open MeasureTheory ProbabilityTheory

namespace ProdMomentConc

/-- **Expectation bound `E L_k ≤ d_R k`** (§A.2).
Saks, Srinivasan, Valieva, *Concentration from Product Moments via an Additional Element of
Randomness*, arXiv:2608.04125 (held version, sha256 5218e9d0…), §A.2, p.36: "E Lk ≤ E_S[∑_{i∈I} deg(i)] = ∑ᵢ deg(i) Pr[i ∈ I] = (k/n) ∑ᵢ deg(i) = dR k".

For `I` a uniformly random `k`-subset of `[n]` (`k ≤ n`), the expected number of underlying
variables read by the outputs in `I` is at most `d_R k`, where `d_R` is the average right degree.

**Formalization Note.** `L_k = Lk P I`, `I ∼ kSubsetLaw n k`, `d_R = dR P = (∑ᵢ |Pᵢ|)/n`. -/
theorem expect_Lk_le {m n : ℕ} (P : Fin n → Finset (Fin m)) (k : ℕ) (hkn : k ≤ n) :
    ∫ S, (Lk P S : ℝ) ∂(kSubsetLaw n k) ≤ dR P * (k : ℝ) := by sorry

end ProdMomentConc
