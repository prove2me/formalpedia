-- Prove2me | Theorems.Thm_ProdMomentConc_lemma_A_2_ii_eps_L
-- name    : ProdMomentConc.lemma_A_2_ii_eps_L
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T09:13:59.09353+00:00
-- url     : https://prove2.me/theorems/24dd1ed1-21a4-4313-b3f3-ae194b4e6099
-- title:
--   Lemma A.2 (ii), second estimate — the neighbourhood size $L_k$ rarely exceeds $r$
-- statement:
--   Consider the bipartite dependency graph with read sets $P_1,\dots,P_n \subseteq [m]$, in which every output reads at most $\Delta_R$ underlying variables and every underlying variable is read by some output. Let $\chi$ be the fractional chromatic number of the auxiliary graph, let $1 \le k \le n$, let $r$ be a natural number with $r > d_R k$, and let $I$ be a uniformly random $k$-subset of $[n]$. Then
--
--   $$
--   \Pr_I[L_k > r] \le \exp\Big(-(r - d_R k)^2 \max\Big\{\frac{1}{2k\Delta_R^2}, \frac{2}{m\chi}\Big\}\Big),
--   $$
--
--   that is, $\varepsilon_L := \Pr[L_k > r]$ satisfies $\ln(1/\varepsilon_L) \ge (r - d_R k)^2\max\{1/(2k\Delta_R^2), 2/(m\chi)\}$.
--
--   It combines the Azuma estimate, Janson's estimate (13) and $\mathbb E L_k \le d_R k$. Together with condition (9) of Theorem 3.5 it gives the second hypothesis of Lemma A.2 (i).
--
--   **Formalization Note** $L_k$ is `Lk P I` with $I \sim$ `kSubsetLaw n k`; $d_R$ is `dR P`; $\chi$ is `OAI.LinearListHadwiger.Fractional.number (auxGraph P)`.
--
--   Differences from the source:
--   - encoding: ln(1/ε_L) ≥ c with Pr[L_k > r] ≤ ε_L → Pr_I[L_k > r] ≤ exp(−c); reason: equivalent, and defined when the probability is 0
--   - generalization: stated in the setting of Theorem 3.5 (r-wise independent bits, outputs with mean p, left degrees ≤ Δ_L, 1 ≤ r ≤ m, r ≥ Δ_R) → only the right-degree bound, the no-isolated-variable convention, 1 ≤ k ≤ n and r > d_R k; reason: L_k and its law depend only on the graph; with the other hypotheses added it is the source's statement
-- source:
--   Saks, Srinivasan, Valieva, Concentration from Product Moments via an Additional Element of Randomness, arXiv:2608.04125 (held version, sha256 5218e9d0405f975413d3e2dd2c4c9d6b43c772029e645965afee1cd619ae38aa), Lemma A.2 (ii), second estimate, p.34 (PDF p.34); proof pp.35–36

import Mathlib
import Definitions.Def_OAIQWLLH000
import Definitions.Def_ProdMomentConc_edgeCount
import Definitions.Def_ProdMomentConc_auxGraph
import Definitions.Def_ProdMomentConc_kSubsetLaw
import Definitions.Def_ProdMomentConc_Lk

open MeasureTheory ProbabilityTheory

namespace ProdMomentConc

/-- **Lemma A.2 (ii), second estimate: the neighbourhood size.**
Saks, Srinivasan, Valieva, *Concentration from Product Moments via an Additional Element of
Randomness*, arXiv:2608.04125 (held version, sha256 5218e9d0…), Lemma A.2 (ii), p.34 (proof pp.35–36).

For the bipartite dependency graph (right degrees at most `ΔR`, every left vertex of positive
degree), a positive integer `k ≤ n`, `I` a uniformly random `k`-subset of `[n]`, and `r > d_R k`,
`ε_L := Pr[L_k > r]` satisfies `ln(1/ε_L) ≥ (r − d_R k)² max{1/(2kΔR²), 2/(mχ)}`, with `χ` the
fractional chromatic number of the auxiliary graph.

**Formalization Note.** Stated in the equivalent form
`Pr[L_k > r] ≤ exp(−(r − d_R k)² max{1/(2kΔR²), 2/(mχ)})`. `L_k = Lk P I`, `I ∼ kSubsetLaw n k`,
`d_R = dR P`, `χ = OAI.LinearListHadwiger.Fractional.number (auxGraph P)`; `r` is a natural number
as in the paper. -/
theorem lemma_A_2_ii_eps_L {m n : ℕ} (P : Fin n → Finset (Fin m)) (ΔR : ℕ)
    (hΔR : ∀ i, (P i).card ≤ ΔR) (hused : ∀ j, ∃ i, j ∈ P i) (r k : ℕ) (hk : 1 ≤ k)
    (hkn : k ≤ n) (hrk : dR P * (k : ℝ) < (r : ℝ)) :
    (kSubsetLaw n k).real {S | r < Lk P S} ≤
      Real.exp (-(((r : ℝ) - dR P * (k : ℝ)) ^ 2 *
        max (1 / (2 * (k : ℝ) * (ΔR : ℝ) ^ 2))
          (2 / ((m : ℝ) * OAI.LinearListHadwiger.Fractional.number (auxGraph P))))) := by sorry

end ProdMomentConc
