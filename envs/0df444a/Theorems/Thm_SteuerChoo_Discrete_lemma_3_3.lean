-- Prove2me | Theorems.Thm_SteuerChoo_Discrete_lemma_3_3
-- name    : SteuerChoo.Discrete.lemma_3_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T16:46:31.917789+00:00
-- url     : https://prove2.me/theorems/faf068c7-6478-4238-aba8-6de6c83a93de
-- title:
--   Lemma 3.3 (corrected) — α_pp < α_pq for every z^q ∈ Z with z^q ≠ zᵖ and z^q ≰ zᵖ
-- statement:
--   Let $k \ge 1$, let $Z \subset \mathbb R^k$ be finite with nondominated set $N$, and let $z^*$ be an ideal criterion vector for $Z$. Let $z^p \in N$ with weights $\lambda^p$ of (b), and for $z^q \in Z$ let $\alpha_{pq} = \max_i \lambda^p_i(z^*_i - z^q_i)$. If $z^q \ne z^p$ and $z^q \not\le z^p$, then
--   $$\alpha_{pp} < \alpha_{pq}.$$
--
--   So under the weights $\lambda^p$ the vector $z^p$ is strictly closer to $z^*$, in the weighted Tchebycheff sense, than every vector of $Z$ that is not below it. This strict gap is what makes the augmentation coefficient $\rho_p$ of (3.6) positive.
--
--   **Formalization Note** The printed Lemma 3.3 asserts $\alpha_{pp} < \alpha_{pq}$ for all $z^q \in Z$, $q \ne p$. That is false: with $Z = \{(5,3),(5,1),(1,10)\}$, $z^* = (5,10)$ (ideal with $\varepsilon = 0$) and $z^p = (5,3)$, the vector $z^q = (5,1)$ has $\alpha_{pq} = 0 = \alpha_{pp}$. The added hypothesis $z^q \not\le z^p$ is the correction (for $z^q \le z^p$ one only has $\alpha_{pp} \le \alpha_{pq}$). Theorems 3.4 and 3.7 are unaffected, because for $z^q \le z^p$, $z^q \ne z^p$ the augmentation term alone separates the two. $S$, $f$ and $\alpha$ are eliminated as in the definitions.
-- source:
--   Steuer and Choo, An Interactive Weighted Tchebycheff Procedure for Multiple Objective Programming, Math. Programming 26 (1983) 326–344, https://doi.org/10.1007/BF02591870, p. 331, Lemma 3.3 (with assumptions (a)–(d), pp. 330–331); corrected, see Formalization Note

import Mathlib
import Definitions.Def_SteuerChoo_Discrete_Nondominated
import Definitions.Def_SteuerChoo_Discrete_IdealVector
import Definitions.Def_SteuerChoo_Discrete_Tchebycheff
import Definitions.Def_SteuerChoo_Discrete_Weights

namespace SteuerChoo.Discrete

/-- **Lemma 3.3** (Steuer–Choo 1983, p. 331), corrected: under (a)–(d), with `z*` an ideal
criterion vector, `zᵖ ∈ N`, `z^q ∈ Z`, `z^q ≠ zᵖ` and `z^q ≰ zᵖ`, we have `α_pp < α_pq`. The printed
lemma omits `z^q ≰ zᵖ` and is false without it. -/
theorem lemma_3_3 {k : ℕ} [NeZero k] (Z : Finset (Fin k → ℝ)) (zstar : Fin k → ℝ)
    (hideal : IsIdealVector Z zstar) (zp : Fin k → ℝ) (hp : zp ∈ nondominated Z)
    (zq : Fin k → ℝ) (hq : zq ∈ Z) (hne : zq ≠ zp) (hnle : ¬ zq ≤ zp) :
    alphaPQ zstar zp zp < alphaPQ zstar zp zq := by sorry

end SteuerChoo.Discrete
