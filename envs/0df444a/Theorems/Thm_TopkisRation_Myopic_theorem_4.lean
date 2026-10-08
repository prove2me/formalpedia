-- Prove2me | Theorems.Thm_TopkisRation_Myopic_theorem_4
-- name    : TopkisRation.Myopic.theorem_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:50:52.78686+00:00
-- url     : https://prove2.me/theorems/bc42291d-64e6-401e-823d-5dacc14168cf
-- title:
--   Theorem 4, p. 175 — nondecreasing myopic levels give optimal ordering and rationing
-- statement:
--   Consider ordering periods $m,\ldots,N$ under the paper's standing assumptions. Let $v=c_{N+1}$, and choose for each period a myopic level $\bar y_i$ according to the rule that it is any nonnegative minimum of $g^i$, or $+\infty$ when no minimum exists. If
--
--   $$\bar y_m\le\bar y_{m+1}\le\cdots\le\bar y_N,$$
--
--   then (a) $\bar y_m$ is finite and, from any net stock $w$, ordering to $w\vee\bar y_m$ is optimal among all levels at least $w^+$. If $m<N$ and the stock at the beginning of period $m$ is at most $\bar y_{m+1}$, then (b) the optimal rationing decisions in every interval of that period are exactly the optimal decisions for the single-period model with terminal costs $v_1\equiv0$ and $v_2(y)=-c_{m+1}y$.
--
--   The result identifies when both dynamic ordering and rationing can be computed from single-period cost functions.
--
--   **Formalization Note** Part (b) compares the sets of minimizers of recursion (1) at every interval and every feasible state whose stock does not exceed $\bar y_{m+1}$. Stock does not rise within a period. The condition $\bar y_{m+1}<\infty$ follows from the theorem's hypotheses; the statement expresses (b) for every real value equal to that level.
-- source:
--   Topkis, Optimal ordering and rationing policies in a nonstationary dynamic inventory model with n demand classes, Management Science 15 (1968), p. 175, Theorem 4

import Definitions.Def_TopkisRation_Myopic_MultiPeriod

namespace TopkisRation.Myopic

variable {n : ℕ}

/-- Theorem 4, p. 175: monotone myopic levels give optimal ordering and, under the stock bound, rationing. -/
theorem theorem_4 (Q : MultiModel n) (hQ : Q.Standing)
    (hv : Q.v = Q.c (Q.N + 1))
    (ybar : ℕ → WithTop ℝ)
    (hy : ∀ i ∈ Finset.Icc 1 Q.N, IsMyopicLevel (Q.gmyopic i) (ybar i))
    (m : ℕ) (hm : m ∈ Finset.Icc 1 Q.N)
    (hmono : MonotoneOn ybar (Set.Icc m Q.N)) :
    (∃ y : ℝ, ybar m = y ∧
      ∀ w z : ℝ, max w 0 ≤ z → Q.gtilde m (max w y) ≤ Q.gtilde m z) ∧
    (m < Q.N → ∀ y' : ℝ, ybar (m + 1) = y' →
      ∀ t ∈ Finset.Icc 1 (Q.P m).k, ∀ z : ℝ, 0 ≤ z → z ≤ y' →
      ∀ B : Fin n → ℝ, 0 ≤ B → ∀ u ∈ TopkisRation.Levels.feasible z B,
      let Ma := (Q.P m).withSalvage (fun _ => 0)
        (fun y => -Q.c (m + 1) * y + Q.C (m + 1) y)
      let Ml := (Q.P m).withSalvage (fun _ => 0)
        (fun y => -Q.c (m + 1) * y)
      IsMinOn (Ma.obj t (Ma.g (t - 1)) z B) (TopkisRation.Levels.feasible z B) u ↔
        IsMinOn (Ml.obj t (Ml.g (t - 1)) z B) (TopkisRation.Levels.feasible z B) u) := by sorry

end TopkisRation.Myopic
