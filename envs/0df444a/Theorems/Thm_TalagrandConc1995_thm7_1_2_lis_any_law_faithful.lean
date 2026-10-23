-- Prove2me | Theorems.Thm_TalagrandConc1995_thm7_1_2_lis_any_law_faithful
-- name    : TalagrandConc1995.thm7_1_2_lis_any_law_faithful
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-23T03:19:16.815439+00:00
-- url     : https://prove2.me/theorems/bf3a3460-6508-46cc-9eb4-b54906c8b29b
-- title:
--   Theorem 7.1.2 — concentration of the longest increasing subsequence, for an arbitrary law on $[0,1]$
-- statement:
--   Let $\mu$ be any probability measure on $[0,1]$, let $X_1,\dots,X_N$ be independent with law $\mu$, realised as the coordinates of $[0,1]^N$ under $P=\mu^{\otimes N}$. Let $L_N=L_N(X_1,\dots,X_N)$ be the length of the longest increasing subsequence, that is, the largest $p$ for which there are $i_1<\dots<i_p$ with $X_{i_1}\le\dots\le X_{i_p}$, and let $M$ be a median of $L_N$. Then for every $u>0$
--
--   $$P(L_N\ge M+u)\le 2\exp\Big(-\frac{u^2}{4(M+u)}\Big),\qquad P(L_N\le M-u)\le 2\exp\Big(-\frac{u^2}{4M}\Big).$$
--
--   This is Theorem 7.1.2 of Talagrand (1995) as stated in the paper, where $\mu$ is the arbitrary law of the paper's standing setting. The existing theorem TalagrandConc.Subsequences.lis_concentration proves the same bounds under the additional assumption that $\mu$ has no atoms (the case in which $L_N$ has the law of the longest increasing subsequence of a uniform random permutation).
--
--   **Formalization Note** When $M=0$ (possible only for $N=0$), Lean's division gives $u^2/(4M)=0$; the event $\{L_N\le -u\}$ is then empty.
-- source:
--   Talagrand, Concentration of measure and isoperimetric inequalities in product spaces, Publ. Math. IHÉS 81 (1995), doi:10.1007/BF02699376, p. 153, Theorem 7.1.2, Eqs. (7.1.3)–(7.1.4)

import Mathlib
import Definitions.Def_TalagrandConc_ConvexHull_Basic
import Definitions.Def_TalagrandConc_Subsequences_Basic

open MeasureTheory
open scoped ENNReal

theorem TalagrandConc1995.thm7_1_2_lis_any_law_faithful {N : ℕ} (μ : Measure unitInterval)
    [IsProbabilityMeasure μ] (M : ℝ)
    (hM : TalagrandConc.BinPacking.IsMedian (Measure.pi fun _ : Fin N => μ)
      (fun x => (TalagrandConc.Subsequences.lis x : ℝ)) M)
    (u : ℝ) (hu : 0 < u) :
    (Measure.pi fun _ : Fin N => μ) {x | M + u ≤ (TalagrandConc.Subsequences.lis x : ℝ)} ≤
        ENNReal.ofReal (2 * Real.exp (-(u ^ 2 / (4 * (M + u))))) ∧
      (Measure.pi fun _ : Fin N => μ) {x | (TalagrandConc.Subsequences.lis x : ℝ) ≤ M - u} ≤
        ENNReal.ofReal (2 * Real.exp (-(u ^ 2 / (4 * M)))) := by sorry
