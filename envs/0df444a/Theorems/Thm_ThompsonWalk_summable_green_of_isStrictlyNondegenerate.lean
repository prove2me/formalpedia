-- Prove2me | Theorems.Thm_ThompsonWalk_summable_green_of_isStrictlyNondegenerate
-- name    : ThompsonWalk.summable_green_of_isStrictlyNondegenerate
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-03T05:58:13.010988+00:00
-- url     : https://prove2.me/theorems/5047d99f-c97b-4c56-b900-79ce36f39dd3
-- title:
--   Kaimanovich, Theorem 25 — a strictly non-degenerate walk on Thompson's F is transient on the dyadic rationals
-- statement:
--   Let $\mu$ be a finitely supported, strictly non-degenerate probability measure on Thompson's group $F$, let $y \in (0,1)$ be a dyadic rational, and let $A$ be a finite set of real numbers. Then
--   $$\sum_{n \ge 0} \Pr\bigl[g_n^{-1}(y) \in A\bigr] < \infty, \qquad g_n = h_1 h_2 \cdots h_n,$$
--   where the $h_i$ are independent with law $\mu$: the walk $y \mapsto g_n^{-1}(y)$ on the dyadic rationals of $(0,1)$ visits $A$ only finitely often on average, so it is transient.
--
--   In the Lean, $\mu$ is a finitely supported function `F →₀ ℝ` with `ThompsonAmenability.IsProbability` and `ThompsonAmenability.IsStrictlyNondegenerate`; the law of $g_n$ is the $n$-th power of $\mu$ in the monoid algebra (`MonoidAlgebra.ofCoeff μ ^ n`), and the probability is the sum of its weights $w$ over the elements $g$ with $g^{-1}(y) \in A$. $F$ acts on $\mathbb R$ by `CannonFloydParry.extend` (as on $[0,1]$, the identity outside).
--
--   Kaimanovich states it on p. 21: "Let $\mu$ be a strictly non-degenerate probability measure on the group $\widetilde F$. Then the induced random walk $(\Gamma, \mu)$ is transient." There $\widetilde F$ is $F$ conjugated to act on $\mathbb R$, written in postfix notation, $(g_1 g_2)(\gamma) = g_2(g_1(\gamma))$, and the induced walk on the dyadic rationals moves $\gamma$ to $g(\gamma)$ (§3.A, p. 19). The map $g \mapsto g^{-1}$ is an isomorphism from that postfix group to the group with the usual composition, and it turns the induced walk into $y \mapsto g_n^{-1}(y)$ as above, with $\mu$ replaced by its image under inversion; strict non-degeneracy is preserved by inversion. The statement here is the finitely supported case, written as finiteness of the expected number of visits to a finite set.
-- source:
--   Kaimanovich, V. A., Thompson's group F is not Liouville, in Groups, Graphs and Random Walks, LMS Lecture Note Ser. 436 (2017) 300–342, https://doi.org/10.1017/9781316576571.013 (arXiv:1602.02971v3, whose page numbers are used), p. 21, Theorem 25, for finitely supported μ

import Mathlib
import Definitions.Def_CannonFloydParry
import Definitions.Def_ThompsonAmenability

namespace ThompsonWalk

theorem summable_green_of_isStrictlyNondegenerate (μ : CannonFloydParry.F →₀ ℝ)
    (hμ : ThompsonAmenability.IsProbability μ) (hnd : ThompsonAmenability.IsStrictlyNondegenerate μ)
    (y : ℝ) (hy : 0 < y ∧ y < 1 ∧ CannonFloydParry.IsDyadic y) (A : Finset ℝ) :
    Summable fun n : ℕ => ((MonoidAlgebra.ofCoeff μ) ^ n).coeff.sum fun g w =>
      if CannonFloydParry.extend ((g⁻¹ : CannonFloydParry.F) : CannonFloydParry.UI ≃o CannonFloydParry.UI) y ∈ A
      then w else 0 := by
  sorry

end ThompsonWalk
