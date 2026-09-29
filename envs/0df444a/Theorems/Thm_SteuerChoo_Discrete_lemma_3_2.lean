-- Prove2me | Theorems.Thm_SteuerChoo_Discrete_lemma_3_2
-- name    : SteuerChoo.Discrete.lemma_3_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T16:45:56.081781+00:00
-- url     : https://prove2.me/theorems/d8abde9d-c6d5-43d9-97a7-329664dd79a0
-- title:
--   Lemma 3.2 (corrected) — no z^q ≰ zᵖ of Z other than zᵖ lies in Φ(α_pp)
-- statement:
--   Let $k \ge 1$, let $Z \subset \mathbb R^k$ be finite with nondominated set $N$, and let $z^*$ be an ideal criterion vector for $Z$. Let $z^p \in N$, let $\lambda^p$ be the weights of (b) and $\alpha_{pp} = \max_i \lambda^p_i(z^*_i - z^p_i)$. If $z^q \in Z$, $z^q \ne z^p$ and $z^q \not\le z^p$ (some coordinate of $z^q$ exceeds that of $z^p$), then
--   $$z^q \notin \Phi(\alpha_{pp}) = \{z \in \mathbb R^k \mid z_i \ge z^*_i - \alpha_{pp}/\lambda^p_i \text{ whenever } \lambda^p_i > 0\}.$$
--
--   The lemma says that $\Phi(\alpha_{pp})$, the smallest Tchebycheff level set reaching $z^p$, contains no other vector of $Z$ that could compete with $z^p$; it feeds Lemma 3.3 and hence Theorem 3.4.
--
--   **Formalization Note** The printed Lemma 3.2 asserts that *no* $z^q \in Z$, $z^q \ne z^p$, lies in $\Phi(\alpha_{pp})$. That is false: for $Z = \{(5,3), (5,1), (1,10)\}$ and $z^* = (5,10)$ (ideal with $\varepsilon = 0$), $z^p = (5,3) \in N$ has $\lambda^p = (1,0)$, $\alpha_{pp} = 0$, and $z^q = (5,1) \in \Phi(0) = \{z \mid z_1 \ge 5\}$. The proof's Case 2 claims $z^p$ is the only member of $Z$ whose $j$-th component reaches $z^*_j$, but the $\varepsilon$-rule only constrains nondominated vectors. The hypothesis $z^q \not\le z^p$ is the correction; it excludes exactly the dominated vectors lying below $z^p$, and with it the statement holds (in the paper's Case 1, where $z^p_i \ne z^*_i$ for all $i$, the printed statement is true as it stands). The printed hypothesis "$z^q \ne z^q$" in (a) is a misprint for $z^q \ne z^p$. $S$, $f$ and $\alpha$ are eliminated as in the definitions.
-- source:
--   Steuer and Choo, An Interactive Weighted Tchebycheff Procedure for Multiple Objective Programming, Math. Programming 26 (1983) 326–344, https://doi.org/10.1007/BF02591870, p. 331, Lemma 3.2 (with assumptions (a)–(c), p. 330); corrected, see Formalization Note

import Mathlib
import Definitions.Def_SteuerChoo_Discrete_Nondominated
import Definitions.Def_SteuerChoo_Discrete_IdealVector
import Definitions.Def_SteuerChoo_Discrete_Tchebycheff
import Definitions.Def_SteuerChoo_Discrete_Weights

namespace SteuerChoo.Discrete

/-- **Lemma 3.2** (Steuer–Choo 1983, p. 331), corrected: under (a)–(c), with `z*` an ideal
criterion vector, `zᵖ ∈ N`, `z^q ∈ Z`, `z^q ≠ zᵖ` and `z^q ≰ zᵖ`, the vector `z^q` does not lie in
`Φ(α_pp)` for the weights `λᵖ` of (b). The printed lemma omits `z^q ≰ zᵖ` and is false without it. -/
theorem lemma_3_2 {k : ℕ} [NeZero k] (Z : Finset (Fin k → ℝ)) (zstar : Fin k → ℝ)
    (hideal : IsIdealVector Z zstar) (zp : Fin k → ℝ) (hp : zp ∈ nondominated Z)
    (zq : Fin k → ℝ) (hq : zq ∈ Z) (hne : zq ≠ zp) (hnle : ¬ zq ≤ zp) :
    zq ∉ Phi (lamP zstar zp) zstar (alphaPQ zstar zp zp) := by sorry

end SteuerChoo.Discrete
