-- Prove2me | Theorems.Thm_SethiChengSS_Finite_Supplement_theorem_5_2
-- name    : SethiChengSS.Finite.Supplement.theorem_5_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T09:29:07.135026+00:00
-- url     : https://prove2.me/theorems/528965d7-5c43-4a18-a7a3-8e285fe8bb95
-- title:
--   Theorem 5.2 — lower semicontinuity and B₀ minimizers
-- statement:
--   Consider the §2 model with a finite real storage capacity $B$, penetration level $C_{\min}$, $0<\beta<1$ and $A_n^i=C_{\min}+\Phi_{i,n}^{-1}(1-\beta)\le B$. The DP equations (4.9) with (5.2), using their own constrained continuation values and terminal cost $f_N$, define functions satisfying
--   $$v_n^{\mathrm{cap}}(i,\cdot)\text{ is lower semicontinuous on }(-\infty,B],\qquad 0\le n\le N.$$
--   There is a nonnegative feedback selector $\widehat u_n\in B_0$ at each nonterminal date, feasible for every $i$ and $x\le B$, with
--   $$v_n^{\mathrm{cap}}(i,x)=f_n(i,x)+K_n^i\delta(\widehat u_n(i,x))+c_n^i\widehat u_n(i,x)+F_{n+1}(v_{n+1}^{\mathrm{cap}})(i,x+\widehat u_n(i,x)).$$
--   Its action minimizes the right-hand expression over all $u\ge0$ with $A_n^i\le x+u\le B$. The full half-line and all equality cases are included; no (4.1), (4.2), positive unit cost or K-convexity premise is imposed.
--
--   The statement also makes the surrounding model interpretation explicit: for $0<q<1$, the demand-quantile level set is nonempty and bounded below and its infimum attains CDF level $q$. Consequently, at every post-order level $y$,
--   $$\Pr\{y-\xi_n\le C_{\min}\mid i_n=i\}\le\beta\quad\Longleftrightarrow\quad A_n^i\le y.$$
--   The nonempty feasible intervals, lower bounded real infima, finite extended $h_n$ and integrable continuation terms are conclusions, not assumptions.
--
--   This provides the selector and regularity theory needed by Theorem 5.3. In $B_0$, a selector is a pointwise limit of nonnegative continuous functions; measurability alone is not substituted.
--
--   **Formalization Note** Selectors extend nonnegatively to the whole real line, while attainment is required only for $x\le B$. The density assumption gives an atomless continuous CDF, so flat intervals require no strict positivity assumption. The definition of $h_n$ keeps $\inf\varnothing=+\infty$.
--
--   Differences from the source:
--   - reading: The DP is identified as (4.11) in the preceding prose but as (4.9) with (5.2) in Theorem 5.2. → v=f−cx+h uses (4.9), with z from (4.11), h from (5.2), and terminal f_N. reason: The displayed equations and the theorem itself resolve the cross-reference slip without changing a mathematical hypothesis.
--   - encoding: The density quantile converts the chance constraint to y≥A, and feasible DP infima and B_0 selectors are asserted. → Quantile attainment, the chance equivalence, bounded nonempty infima and integrable continuation are included explicitly, alongside l.s.c. and B_0 attainment. reason: These expand the surrounding §5.2 model claims and prevent default real infima or Bochner integrals from trivializing the DP; no extra premise is introduced.
--   - generalization: The service conversion uses the quantile at q=1−β. → The quantile level set is nonempty and bounded below and its infimum attains CDF level q for every q∈(0,1), independently of the chosen β. reason: A density gives a continuous CDF with limits 0 and 1; specializing to q=1−β recovers the complete source claim, including flat CDF intervals.
-- source:
--   Sethi and Cheng, Optimality of (s, S) policies in inventory models with Markovian demand, Oper. Res. 45(6) (1997), DOI 10.1287/opre.45.6.931, p. 936, Theorem 5.2

import Mathlib
import Definitions.Def_SethiChengSS_Finite_Supplement_Capacity

namespace SethiChengSS.Finite.Supplement

open MeasureTheory Filter Topology
open scoped ENNReal

/-- Theorem 5.2 and the service-quantile interpretation immediately preceding it.
No (4.1), (4.2), positive unit cost, or global K-convexity is assumed. -/
theorem theorem_5_2 {L : ℕ} (D : Data L) (T : ServiceData) (N : ℕ)
    (hD : Standing D) (hT : ServiceFeasible D T N) :
    (∀ n < N, ∀ i q, 0 < q → q < 1 →
      {t : ℝ | q ≤ demandCDF D n i t}.Nonempty ∧
      BddBelow {t : ℝ | q ≤ demandCDF D n i t} ∧
      demandCDF D n i (demandQuantile D n i q) = q) ∧
    (∀ n < N, ∀ i y,
      (serviceFailure D T n i y ≤ ENNReal.ofReal T.β ↔ serviceA D T n i ≤ y)) ∧
    (∀ n ≤ N, ∀ i, LowerSemicontinuousOn (capV D T N n i) (Set.Iic T.B)) ∧
    (∀ n < N, ∀ i j y, y ≤ T.B →
      Integrable (fun z => capV D T N (n + 1) j (y - z) * D.φ n i z)
        (volume.restrict (Set.Ioi 0))) ∧
    (∀ n < N, ∀ i x, x ≤ T.B →
      (capLevels D T n i x).Nonempty ∧
      BddBelow (capObjective D n (capV D T N (n + 1)) i x '' capLevels D T n i x) ∧
      capH D T N n i x =
        ((sInf (capObjective D n (capV D T N (n + 1)) i x '' capLevels D T n i x) : ℝ) : EReal) ∧
      (capV D T N n i x : EReal) =
        ((D.f n i x - D.c n i * x : ℝ) : EReal) + capH D T N n i x) ∧
    ∃ û : ℕ → Fin L → ℝ → ℝ,
      ∀ n < N, InB0 (û n) ∧ ∀ i x, x ≤ T.B →
        capAction D T n i x (û n i x) ∧
        capV D T N n i x = D.f n i x + orderCost D n i (û n i x) +
          F D n (capV D T N (n + 1)) i (x + û n i x) ∧
        ∀ u : ℝ, capAction D T n i x u →
          orderCost D n i (û n i x) + F D n (capV D T N (n + 1)) i (x + û n i x) ≤
          orderCost D n i u + F D n (capV D T N (n + 1)) i (x + u) := by sorry

end SethiChengSS.Finite.Supplement
