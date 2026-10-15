-- Prove2me | Theorems.Thm_PrizeAlloc_SingleParam_propagation
-- name    : PrizeAlloc.SingleParam.propagation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T04:34:19.641981+00:00
-- url     : https://prove2.me/theorems/39328908-ffde-44de-932c-0c3442495fca
-- title:
--   pp. 31–32 — propagation: after the first position where φ′ exceeds φ, φ′ is at least φ at every later position
-- statement:
--   Let $\varphi$ be a prize allocation rule satisfying local consistency that, on every two-competitor competition, is the single-parametric rule with a representation $f$ (continuous, non-decreasing, $0\le f(x)\le x$). Let $\varphi'$ be the single-parametric rule with the same representation $f$ on all competitions. Fix a competition $(N,\mathcal R,E)$ and label the competitors $1,\dots,|N|$ by position. Suppose that at position $i$
--   $$\varphi'_j(N,\mathcal R,E)=\varphi_j(N,\mathcal R,E)\ \ (j<i),\qquad \varphi'_i(N,\mathcal R,E)>\varphi_i(N,\mathcal R,E).$$
--   Then
--   $$\varphi'_j(N,\mathcal R,E)\ge\varphi_j(N,\mathcal R,E)\quad\text{for each } j>i.$$
--
--   In the proof of Theorem 2 this step leads to $\sum_j\varphi'_j>\sum_j\varphi_j=E$, the contradiction that proves uniqueness. Since that argument shows the hypotheses can never hold together, this statement records a step of a proof by contradiction, exactly as the paper uses it.
--
--   **Formalization Note** Positions are list indices: the competitor in position $q+1$ is `l[q]` (0-based). The paper's "without loss of generality $\varphi'_i>\varphi_i$" is taken as stated; the case $\varphi'_i<\varphi_i$ is symmetric and is not part of this claim. Anonymity of $\varphi$, which the paper invokes to apply the two-competitor form to $\{i,i+1\}$, is contained in the hypothesis that $\varphi$ follows $f$ on every two-competitor competition.
-- source:
--   Dietzenbacher and Kondratev, Fair and Consistent Prize Allocation in Competitions, arXiv:2008.08985v2, pp. 31–32, proof of Theorem 2, propagation step

import Mathlib
import Definitions.Def_PrizeAlloc_SingleParam_Setting
import Definitions.Def_PrizeAlloc_SingleParam_Rules

namespace PrizeAlloc.SingleParam

theorem propagation {U : Type*} [DecidableEq U]
    (φ φ' : List U → ℝ → U → ℝ) (f : ℝ → ℝ)
    (hφ : PrizeAlloc.Interval.IsPrizeRule φ) (hLC : LocallyConsistent φ) (hf : IsRepresentation f)
    (h2 : ∀ l E, PrizeAlloc.Interval.IsRanking l → l.length = 2 → 0 ≤ E →
      ∃ x, 0 ≤ x ∧ (∑ k ∈ Finset.range l.length, f^[k] x) = E ∧
        ∀ i ∈ l, φ l E i = f^[PrizeAlloc.Interval.pos l i - 1] x)
    (hφ' : PrizeAlloc.Interval.IsPrizeRule φ') (h' : IsSingleParamRuleWith f φ')
    (l : List U) (hl : PrizeAlloc.Interval.IsRanking l) (E : ℝ) (hE : 0 ≤ E) (q : ℕ) (hq : q < l.length)
    (hbefore : ∀ r (hr : r < q), φ' l E (l[r]'(hr.trans hq)) = φ l E (l[r]'(hr.trans hq)))
    (hgt : φ l E l[q] < φ' l E l[q]) :
    ∀ r (hr : r < l.length), q < r → φ l E l[r] ≤ φ' l E l[r] := by sorry

end PrizeAlloc.SingleParam
