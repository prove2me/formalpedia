-- Prove2me | Theorems.Thm_RevRedSAT_lemma_B_4
-- name    : RevRedSAT.lemma_B_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T04:47:32.872958+00:00
-- url     : https://prove2.me/theorems/daa0cdd2-37e9-4e18-93de-db3f980dea6c
-- title:
--   Lemma B.4 — a feasible family has measure $\mu(\mathcal F)>k/4$
-- statement:
--   Let $d\ge2$, $\delta=2^{-j}$ with $j\ge2$, and $k>0$. Let $\mathcal F$ be a reduced family of nonempty sets of size at most $d$ (the standing assumptions of App. B). If $\mathcal F$ has a hitting set of size at most $k$, then
--
--   $$\mu(\mathcal F)=k-\sum_{s=1}^{\tau(\mathcal F)}w_s|\mathcal F_s|>\frac k4.$$
--
--   This justifies discarding recursion nodes of nonpositive measure in the sparsifier.
--
--   Differences from the source:
--   - encoding: δ = 2^{−j}, A = 2d/δ, weights and thresholds (17) → j : ℕ with δ = (2^j)^{−1}; real-valued t_p, w_s, µ; reason: same quantities
-- source:
--   Kundu, Panolan, Saurabh, Xue, Zehavi, Reverse Reductions: From Faster SAT to Subexponential Algorithms, STOC 2027 submission (held manuscript, sha256 7bf9a5af…), Lemma B.4, p.88 (printed) = PDF p.90; standing assumptions p.87

import Mathlib
import Definitions.Def_AlgebraicFPT_HittingSet_HittingSets
import Definitions.Def_RevRedSAT_mu

set_option autoImplicit false

namespace RevRedSAT

/-- **Lemma B.4 (feasible families have large measure).**
Kundu, Panolan, Saurabh, Xue, Zehavi, *Reverse Reductions: From Faster SAT to Subexponential
Algorithms*, STOC 2027 submission (held manuscript, sha256 7bf9a5af…), Lemma B.4, p.88: "If F has a hitting set of size at most k > 0, then µ(F) > k/4."

Standing assumptions of App. B (p.87): `d ≥ 2`, `δ = 2^{−j}` with `j ≥ 2`, `k > 0`, all hyperedges
nonempty, and every family of the recursion is reduced and of rank at most `d`. For such a family
`F` with a hitting set of size at most `k`, `µ(F) = k − Σ_{s=1}^{τ(F)} w_s|F_s| > k/4`.

**Formalization Note** `µ` is real-valued and computed with the thresholds and weights of (17)
(`tp`, `ws`) and `τ(F)` of Definition B.3. -/
theorem lemma_B_4 (d j n k : ℕ) (hd : 2 ≤ d) (hj : 2 ≤ j) (hk : 0 < k)
    (F : Finset (Finset (Fin n))) (hrank : ∀ S ∈ F, S.card ≤ d) (hne : ∀ S ∈ F, S.Nonempty)
    (hred : IsReduced F)
    (hX : ∃ X : Finset (Fin n), AlgebraicFPT.HittingSet.IsHitting F X ∧ X.card ≤ k) :
    (k : ℝ) / 4 < mu d j k F := by sorry

end RevRedSAT
