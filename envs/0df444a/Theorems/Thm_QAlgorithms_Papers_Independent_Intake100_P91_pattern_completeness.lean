-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P91_pattern_completeness
-- name    : QAlgorithms.Papers.Independent.Intake100.P91.pattern_completeness
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T11:12:55.882579+00:00
-- url     : https://prove2.me/theorems/f2077c88-514e-45cf-8a02-e5bfb79fd46f
-- title:
--   The four Pattern Rules exhaust all qubit edges and equal Louck
-- statement:
--   Consider any adjacent qubit GT patterns $(r,s;a)$ and $(R,S;b)$, with nonnegative integral entries satisfying $s\le a\le r$ and $S\le b\le R$, connected by the precise addition rule (16). Exactly one top-row entry increases by one. The edge is covered by Rule 1 ($s=S=0$), Rule 2 ($s=0,S=1$), Rule 3 ($s=S>0$), or Rule 4 ($s>0,S=s+1$), with $R=r+1$ in the first and third cases and $R=r$ in the other cases. In every case $b=a$ or $b=a+1$.
--
--   Let $A$ denote the independent real Louck product, and $P$ the following result of column deletion followed by Rule 1 or Rule 2:
--
--   $$
--   P(r,s,a;R,S,b)=
--   \begin{cases}
--   \sqrt{(R-b)/(R-s)},&S=s,\ a=b,\\
--   \sqrt{(b-s)/(R-s)},&S=s,\ b=a+1,\\
--   \sqrt{(b-S+1)/(R-S+2)},&S=s+1,\ a=b,\\
--   -\sqrt{(R-b+1)/(R-S+2)},&S=s+1,\ b=a+1.
--   \end{cases}
--   $$
--
--   For every such edge the relevant denominator is positive and
--
--   $$
--   A(r,s,a;R,S,b)=P(r,s,a;R,S,b).
--   $$
--
--   Thus the rules are universally exhaustive and agree with Louck, including edges out of the empty pattern. No numerical or asymptotic speedup bound is asserted.
-- source:
--   A Multigraph Approach for Performing the Quantum Schur Transform, arXiv:2204.10694v1, PDF p. 18, Appendix A, pp.18–20; §4.1

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P91

noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P91

open scoped BigOperators

attribute [local instance] Classical.propDecidable

/-- Appendix A, PDF pp.18-20: the four rules cover EVERY qubit graph edge,
including vacuum edges, and give exactly the independently defined Louck
coefficient. This is universal coverage, without a speedup claim. -/
theorem pattern_completeness (r s a R S b : ℕ) (h : QubitEdge r s a R S b) :
    ((s = 0 ∧ S = 0 ∧ R = r+1) ∨
     (s = 0 ∧ S = 1 ∧ R = r) ∨
     (0 < s ∧ S = s ∧ R = r+1) ∨
     (0 < s ∧ S = s+1 ∧ R = r)) ∧
    (b = a ∨ b = a+1) ∧
    (if S = s then 0 < (R : ℝ) - s else 0 < (R : ℝ) - S + 2) ∧
    qubitLouck r s a R S b = patternAmplitude r s a R S b := by sorry

end QAlgorithms.Papers.Independent.Intake100.P91

end
