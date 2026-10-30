-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P28_universal2_moment_bound
-- name    : QAlgorithms.Papers.Independent.Advance50.P28.universal2_moment_bound
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T10:44:55.013981+00:00
-- url     : https://prove2.me/theorems/767714fc-335a-4c62-a783-2269ed8fbe42
-- title:
--   Theorem 1 (12): paper headline
-- statement:
--   Let $P\ge0$ be a subdistribution on a finite nonempty $A$, with total mass $m\le1$. Let $M\ge1$ and choose a hash $f_X:A\to\{1,\ldots,M\}$ independently of the source, with collision probability at most $1/M$ for every pair of distinct source letters. For every $0\le s\le1$,
--   $$\mathbb E_X\|f_{X*}P-mU_M\|_1\le3M^{s/(1+s)}\left(\sum_aP(a)^{1+s}\right)^{1/(1+s)}.$$
--   This moment form includes $s=0$ and the zero subdistribution, and gives the paper's universal privacy-amplification bound without a balancing assumption. Here $U_M$ is uniform and $\|\cdot\|_1$ is the full $L^1$ norm.
-- source:
--   Tight exponential analysis of universally composable privacy amplification and its applications, arXiv:1010.1358v5, PDF p. 4, Theorem 1 (12): paper headline

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P28

noncomputable section

open MeasureTheory Filter

open scoped BigOperators ENNReal Topology

namespace QAlgorithms.Papers.Independent.Advance50.P28

open QAlgorithms.Papers.Independent.Information100.P56 (IsLaw)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Hayashi, PDF p.4, Theorem 1, (12): no balance or Condition 3 is required. -/
theorem universal2_moment_bound {A : Type*} [Fintype A] [Nonempty A]
    {M : ℕ} (hM : 0 < M) (h : HashEnsemble A M) (hu : Universal2 h)
    (P : A → ℝ) (hP : IsSubLaw P) (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    expectedError h P ≤ 3 * (M : ℝ) ^ (s / (1 + s)) *
      (renyiPowerSum P s) ^ (1 / (1 + s)) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P28

end
