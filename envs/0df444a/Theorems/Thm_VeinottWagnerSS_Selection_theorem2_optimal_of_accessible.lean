-- Prove2me | Theorems.Thm_VeinottWagnerSS_Selection_theorem2_optimal_of_accessible
-- name    : VeinottWagnerSS.Selection.theorem2_optimal_of_accessible
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-29T14:12:42.287215+00:00
-- url     : https://prove2.me/theorems/b928ce4e-95f7-49e6-b6d2-940f2c7c5aac
-- title:
--   Theorem 2 — a policy of $\mathcal S$ is optimal if the stocks between the two reorder points are accessible from its order-up-to level
-- statement:
--   Let $0 < \alpha < 1$ and consider the inventory model with set-up cost $K \ge 0$, convex one-period cost $G_\alpha$ with $G_\alpha(y) \to \infty$ as $|y| \to \infty$, and i.i.d. integer demands with finite mean. Let $\mathcal S$ be the candidate set of Step ii: the $(s, S)$ policies with $\underline{s} \le s \le \bar{s}$, $\underline{S} \le S \le \bar{S}$ that minimize $\mathcal L_\alpha(S, S - s)$ among such policies, where $\underline{s}, \bar{s}, \underline{S}, \bar{S}$ are the integers of (21)–(23).
--
--   Let $(s^i, S^i)$ and $(s^j, S^j)$ belong to $\mathcal S$. Suppose that $(s^i, S^i)$ is optimal, i.e. it minimizes $a_\alpha(x \mid s, S)$ over all $(s, S)$ policies for every starting stock $x$, and that every integer $x'$ with
--   $$\min(s^i, s^j) \le x' < \max(s^i, s^j)$$
--   is accessible from $S^j$ under $(s^j, S^j)$. Then $(s^j, S^j)$ is optimal.
--
--   The theorem lets the algorithm of the paper certify a policy of $\mathcal S$ as optimal by a reachability check on the demand distribution instead of a comparison of average costs; its Corollaries 2.1 and 2.2 give conditions (e.g. $\varphi(k) > 0$ for $k = 1, \dots, s^n - s^1$) under which this check is automatic.
--
--   **Formalization Note** Policies are pairs $(s, S) \in \mathbb Z \times \mathbb Z$; "optimal" is among all $(s, S)$ policies for every integer starting stock (p. 536). $\mathcal L_\alpha(S, D)$ is $a_\alpha(S - D - 1 \mid S - D, S)$. The bounds are least integers, computed from $G_\alpha$, $K$ and $\alpha$. As for Lemma 1, the paper's standing assumptions are kept.
-- source:
--   Veinott & Wagner, Computing Optimal (s, S) Inventory Policies, Management Sci. 11 (1965), p. 543, Theorem 2 (𝒮 defined p. 536 Step ii and p. 542; bounds p. 537 (21)-(23))

import Mathlib
import Definitions.Def_VeinottWagnerSS_Selection_Model
import Definitions.Def_VeinottWagnerSS_Selection_CandidateSet

namespace VeinottWagnerSS.Selection

/-- Veinott & Wagner (1965), Theorem 2, p. 543: let `0 < α < 1` and let `(sⁱ, Sⁱ)`, `(sʲ, Sʲ)`
be policies of the candidate set `𝒮` of Step ii. If `(sⁱ, Sⁱ)` is optimal, and if each `x'`
with `min(sⁱ, sʲ) ≤ x' < max(sⁱ, sʲ)` is accessible from `Sʲ` under `(sʲ, Sʲ)`, then
`(sʲ, Sʲ)` is optimal. -/
theorem theorem2_optimal_of_accessible (M : Model) (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1)
    (pi pj : ℤ × ℤ) (hpi : pi ∈ candSet M α) (hpj : pj ∈ candSet M α)
    (hopt : Optimal M α pi.1 pi.2)
    (hacc : ∀ x' : ℤ, min pi.1 pj.1 ≤ x' → x' < max pi.1 pj.1 →
      Accessible M pj.1 pj.2 pj.2 x') :
    Optimal M α pj.1 pj.2 := by sorry

end VeinottWagnerSS.Selection
