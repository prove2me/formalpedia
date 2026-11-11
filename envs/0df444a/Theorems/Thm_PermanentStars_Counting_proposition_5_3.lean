-- Prove2me | Theorems.Thm_PermanentStars_Counting_proposition_5_3
-- name    : PermanentStars.Counting.proposition_5_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:55:23.982903+00:00
-- url     : https://prove2.me/theorems/a2033b19-189e-4a7b-ab8a-b3975ebf55b3
-- title:
--   Proposition 5.3 — Effective size at one cutoff
-- statement:
--   Fix valid cutoff data and $r\in R$, and choose $1<c<2$ with $c(c-1)^{r-1}\ge1$. There are $C>0$ and a natural $d$, independent of $n$, such that whenever the standing coverage assumption holds,
--   $$\#\{v:s_r\leadsto v\}\le C(n+1)^d c^n\sum_{p=0}^{\lfloor\alpha_r n\rfloor}\binom np(c-1)^{-p}.$$
--   The left side counts reachable nodes, as required by effective size. It does not count the entire ambient graph. This bound includes the attached gadgets and controls the nursery bookkeeping cost.
--
--   Differences from the source:
--   - encoding: O* of the weighted binomial bound → C(n+1)^d times the same bound, with C,d outside n; reason: fixed-parameter polynomial suppression and finite initial sizes are made explicit
--   - encoding: finite star and nursery states along the source construction → finite bounded coordinate carriers, an optional open marker and isolated impossible states; reason: every source-reachable state has all counts at most n and satisfies the leaf-count invariants; no path contribution is removed
-- source:
--   Radu Curticapean, STOC 2027 submission #1331 (October 2026), Proposition 5.3, PDF/printed p.11

import Definitions.Def_PermanentStars_Counting_Combined

namespace PermanentStars.Counting

/-- Proposition 5.3, (21), p.11. Only reachable nodes are counted; R is fixed. -/
theorem proposition_5_3 (P : Cutoffs) (hP : P.Valid) (r : ℕ) (hr : r ∈ P.R)
    (c : ℝ) (hc : 1 < c) (hc2 : c < 2) (hprod : 1 ≤ c * (c - 1) ^ (r - 1)) :
    ∃ (C : ℝ) (d : ℕ), 0 < C ∧ ∀ (n : ℕ) (coverage : Covers P n),
      ((cutoffABP P r n).effectiveSize : ℝ) ≤
        C * (n + 1 : ℝ) ^ d * c ^ n * binomialBudget n (P.alpha r : ℝ) c := by sorry

end PermanentStars.Counting
