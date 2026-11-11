-- Prove2me | Theorems.Thm_ProdMomentConc_eq_13
-- name    : ProdMomentConc.eq_13
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T09:13:42.899401+00:00
-- url     : https://prove2.me/theorems/90889a6c-ea38-4e40-b5cb-673693ae652e
-- title:
--   Eq. (13) — Janson's tail estimate for $L_k$ via the fractional chromatic number
-- statement:
--   Let $P_1,\dots,P_n \subseteq [m]$ be the read sets of the dependency graph, let $k \le n$, let $I$ be a uniformly random $k$-subset of $[n]$ and $L_k$ the number of underlying variables read by $I$. Let $\chi$ be the fractional chromatic number of the auxiliary graph on $[m]$ (two underlying variables adjacent when they have a common output neighbour). Then for every real $r$,
--
--   $$
--   \Pr[L_k > r] \le \exp\Big(-\frac{2(r - \mathbb E L_k)_+^2}{\chi m}\Big).
--   $$
--
--   In the paper this is Lemma A.1 applied with $V = [m]$ and $Z_j = \mathbf 1[N(j) \cap I \ne \emptyset]$, so that $L_k = \sum_j Z_j$. It is the second of the two estimates of $\varepsilon_L$ in Lemma A.2 (ii), and it improves on Azuma's when the auxiliary graph has small fractional chromatic number.
--
--   **Formalization Note** $\chi$ is the published `OAI.LinearListHadwiger.Fractional.number`: the infimum of the total weight of fractional covers of the vertices by stable sets (no optimal cover is assumed to exist). $(x)_+ = \max(x,0)$. For $m = 0$ the right side is $\exp(0) = 1$.
--
--   Differences from the source:
--   - generalization: r the independence parameter, in the setting of Theorem 3.5 → r any real number, any k ≤ n, no hypothesis on the graph; reason: L_k and χ depend only on the graph; the source's case is an instance
-- source:
--   Saks, Srinivasan, Valieva, Concentration from Product Moments via an Additional Element of Randomness, arXiv:2608.04125 (held version, sha256 5218e9d0405f975413d3e2dd2c4c9d6b43c772029e645965afee1cd619ae38aa), eq. (13), §A.2, p.36 (PDF p.36), following [Jan04]

import Mathlib
import Definitions.Def_OAIQWLLH000
import Definitions.Def_ProdMomentConc_auxGraph
import Definitions.Def_ProdMomentConc_kSubsetLaw
import Definitions.Def_ProdMomentConc_Lk

open MeasureTheory ProbabilityTheory

namespace ProdMomentConc

/-- **(13): Janson's tail estimate for `L_k` via the fractional chromatic number.**
Saks, Srinivasan, Valieva, *Concentration from Product Moments via an Additional Element of
Randomness*, arXiv:2608.04125 (held version, sha256 5218e9d0…), eq. (13), §A.2, p.36.

For `I` a uniformly random `k`-subset of `[n]` (`k ≤ n`) and every threshold `r`,
`Pr[L_k > r] ≤ exp(−2(r − E L_k)₊²/(χm))`, where `χ` is the fractional chromatic number of the
auxiliary graph of Theorem 3.5 (underlying variables adjacent when they share an output).

**Formalization Note.** `L_k = Lk P I`, `I ∼ kSubsetLaw n k`, `E L_k` the Bochner integral of the
bounded function `Lk P`; `(x)₊ = max x 0`; `χ = OAI.LinearListHadwiger.Fractional.number
(auxGraph P)`, an infimum over fractional covers (no optimal cover is assumed). The threshold `r`
is any real number. For `m = 0` the right side is `exp 0 = 1` by Lean's `x / 0 = 0`. -/
theorem eq_13 {m n : ℕ} (P : Fin n → Finset (Fin m)) (k : ℕ) (hkn : k ≤ n) (r : ℝ) :
    (kSubsetLaw n k).real {S | r < (Lk P S : ℝ)} ≤
      Real.exp (-(2 * (max (r - ∫ T, (Lk P T : ℝ) ∂(kSubsetLaw n k)) 0) ^ 2 /
        (OAI.LinearListHadwiger.Fractional.number (auxGraph P) * (m : ℝ)))) := by sorry

end ProdMomentConc
