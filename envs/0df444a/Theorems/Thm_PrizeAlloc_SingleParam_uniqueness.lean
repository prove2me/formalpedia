-- Prove2me | Theorems.Thm_PrizeAlloc_SingleParam_uniqueness
-- name    : PrizeAlloc.SingleParam.uniqueness
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T04:34:17.643006+00:00
-- url     : https://prove2.me/theorems/e88e7ad6-255e-4409-95ba-881dd8b74960
-- title:
--   p. 32 — a locally consistent rule that follows f on two competitors coincides with the single-parametric rule with representation f
-- statement:
--   Let $\varphi$ be a prize allocation rule satisfying local consistency that, on every two-competitor competition, is the single-parametric rule with a representation $f$ (continuous, non-decreasing, $0\le f(x)\le x$). Let $\varphi'$ be the single-parametric rule with representation $f$ on all competitions. Then
--   $$\varphi'(N,\mathcal R,E)=\varphi(N,\mathcal R,E)\quad\text{for each competition }(N,\mathcal R,E).$$
--
--   Together with the two-competitor form and the converse this gives Theorem 2.
--
--   **Formalization Note** Anonymity of $\varphi$ enters only through the hypothesis that $\varphi$ follows $f$ on every two-competitor competition.
-- source:
--   Dietzenbacher and Kondratev, Fair and Consistent Prize Allocation in Competitions, arXiv:2008.08985v2, p. 32, proof of Theorem 2, closing sentence

import Mathlib
import Definitions.Def_PrizeAlloc_SingleParam_Setting
import Definitions.Def_PrizeAlloc_SingleParam_Rules

namespace PrizeAlloc.SingleParam

theorem uniqueness {U : Type*} [DecidableEq U]
    (φ φ' : List U → ℝ → U → ℝ) (f : ℝ → ℝ)
    (hφ : PrizeAlloc.Interval.IsPrizeRule φ) (hLC : LocallyConsistent φ) (hf : IsRepresentation f)
    (h2 : ∀ l E, PrizeAlloc.Interval.IsRanking l → l.length = 2 → 0 ≤ E →
      ∃ x, 0 ≤ x ∧ (∑ k ∈ Finset.range l.length, f^[k] x) = E ∧
        ∀ i ∈ l, φ l E i = f^[PrizeAlloc.Interval.pos l i - 1] x)
    (hφ' : PrizeAlloc.Interval.IsPrizeRule φ') (h' : IsSingleParamRuleWith f φ') :
    ∀ l E, PrizeAlloc.Interval.IsRanking l → 0 ≤ E → ∀ i ∈ l, φ' l E i = φ l E i := by sorry

end PrizeAlloc.SingleParam
