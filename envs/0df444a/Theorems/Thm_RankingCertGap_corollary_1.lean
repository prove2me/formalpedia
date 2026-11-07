-- Prove2me | Theorems.Thm_RankingCertGap_corollary_1
-- name    : RankingCertGap.corollary_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:52:32.643672+00:00
-- url     : https://prove2.me/theorems/3a908f1a-29d8-41d7-b3cd-741cc19f08f4
-- title:
--   Corollary 1, p.17 — monomial safety profile
-- statement:
--   Let $G$ have online degree at most two, and fix an arrival prefix. For every offline node $i$ there exist an integer $p_i\ge0$ and $a_i\in[0,1]$ such that
--
--   $$
--   \Pr[\mathcal E_i\mid Y_i=y]=a_iy^{p_i}\qquad\text{for every }y\in[0,1],
--   $$
--
--   and $a_i=0$ if and only if $\Pr[\mathcal E_i]=0$. The conditional probability fixes the rank of $i$ at $y$ and samples the remaining ranks independently and uniformly on $[0,1]$.
--
--   This monomial profile is the two-parameter state that drives the rest of the degree-two analysis.
--
--   Differences from the source:
--   - encoding: each instance has an arbitrary online arrival order → $J=\mathrm{Fin}\,n$ listed in arrival order; reason: an arbitrary order is a relabelling of $J$; same instances
--   - encoding: strict rank comparisons, ranks distinct with probability one → a tie goes to the least index among minimum-rank neighbours; reason: ties have probability zero, so no probability or expectation changes
--   - encoding: $\Pr[\mathcal E_i\mid Y_i=y]$ in the version "specified ranks are fixed, and the remaining ranks are sampled" → the coordinate $i$ of the rank vector is overwritten by $y$ and the other coordinates are integrated out; reason: this is the printed version; $\texttt{condExp}$ would lose "for every $y$"
-- source:
--   Xu, Certifying Capacity and Gaps of the Rank-Dependent Gain-Sharing Framework for Ranking, arXiv:2610.17545 (held file sha256 75896dd9…), Corollary 1, p.17; p.18

import Mathlib
import Definitions.Def_RankingCertGap_RankingRun
import Definitions.Def_RankingCertGap_Score

open MeasureTheory

namespace RankingCertGap

/-- **Corollary 1 (Monomial safety profile).** Xu, arXiv:2610.17545 (held file sha256 75896dd9…),
Corollary 1, p.17: for every offline node `i` there exist `p_i ∈ ℤ_{≥0}` and `a_i ∈ [0, 1]` with
`Pr[E_i | Y_i = y] = a_i y^{p_i}` for every `y ∈ [0, 1]` (eq. (38)), and `a_i = 0` iff `Pr[E_i] = 0`.

**Formalization Note.** `Pr[E_i | Y_i = y]` is `Inst.condSafe`, the version the page specifies: the
rank of `i` is fixed to `y` and the others are sampled. `0 ^ 0 = 1` in Lean, matching the page's
convention `y⁰ = 1` at `y = 0` (p.18). -/
theorem corollary_1 {m n : ℕ} (G : Inst m n) (hG : G.IsOnlineDegLE 2) (t : ℕ) (ht : t ≤ n)
    (i : Fin m) :
    ∃ (p : ℕ) (a : ℝ), a ∈ Set.Icc (0 : ℝ) 1 ∧
      (∀ y ∈ Set.Icc (0 : ℝ) 1, G.condSafe t i y = a * y ^ p) ∧
      (a = 0 ↔ (rankMeasure m).real (G.safeEvent t i) = 0) := by sorry

end RankingCertGap
