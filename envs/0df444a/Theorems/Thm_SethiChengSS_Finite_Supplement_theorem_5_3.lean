-- Prove2me | Theorems.Thm_SethiChengSS_Finite_Supplement_theorem_5_3
-- name    : SethiChengSS.Finite.Supplement.theorem_5_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T09:31:41.953368+00:00
-- url     : https://prove2.me/theorems/60fbef77-8b92-4d9f-aedc-12d919c1007e
-- title:
--   Theorem 5.3 — bounded capacity/service thresholds
-- statement:
--   In the §2 finite-horizon model with storage capacity $B$, penetration level $C_{\min}$, $0<\beta<1$ and feasible service bounds $A_n^i=C_{\min}+\Phi_{i,n}^{-1}(1-\beta)\le B$, assume the inherited fixed-cost condition (4.1). There are finite real thresholds satisfying every bound
--   $$A_n^i\le s_n^{\prime i}\le S_n^{\prime i}\le B,\qquad n<N,\quad i\in I,$$
--   such that the feedback rule
--   $$\widehat u_n(i,x)=(S_n^{\prime i}-x)\delta(s_n^{\prime i}-x),\qquad x\le B,$$
--   is feasible, belongs to $B_0$, and attains each capacity/service DP infimum. For every $n\le N$, state $i$ and initial surplus $x\le B$, its generated policy is admissible and
--   $$J_n(i,x;\widehat U)=v_n^{\mathrm{cap}}(i,x)=\inf_{U\ \mathrm{capacity/service\ admissible}}J_n(i,x;U).$$
--   It therefore costs no more than any measurable history-dependent constrained policy. This includes arbitrary backlog, $x=B$, $A_n^i=B$ and the terminal-period problem. The rule orders nothing at the threshold $x=s_n^{\prime i}$.
--
--   The result adds the storage/service companion to the finite-horizon goal, using the regularity and selectors of Theorem 5.2. There is no upper-coercivity or positive-unit-cost premise.
--
--   **Formalization Note** The action constraints along history-dependent policies hold almost surely under the model law. The rule is extended by zero for $x>B$, which does not affect the claim: nonnegative demand keeps every feasible post-order surplus at or below $B$. Condition (4.1) is inherited from the K-convexity induction that the printed proof invokes from Theorem 4.1; it is explicit in Lean.
--
--   Differences from the source:
--   - reading: The proof modifies the induction of Theorem 4.1 on the half-line. → The inherited (4.1) fixed-cost inequality is explicit; (4.2) is not assumed. reason: The proof uses (4.1) in the K-convexity induction, while finite capacity replaces upper coercivity.
--   - encoding: The bounded (s,S) feedback is optimal for the constrained model. → Every threshold bound, feasible DP minimum and full history-dependent policy comparison is explicit; history constraints are imposed almost surely. reason: This retains the actual demand law, includes the equality cases and avoids imposing capacity feasibility on impossible negative-demand paths.
-- source:
--   Sethi and Cheng, Optimality of (s, S) policies in inventory models with Markovian demand, Oper. Res. 45(6) (1997), DOI 10.1287/opre.45.6.931, p. 936, Theorem 5.3

import Mathlib
import Definitions.Def_SethiChengSS_Finite_Supplement_Capacity

namespace SethiChengSS.Finite.Supplement

open MeasureTheory Filter Topology
open scoped ENNReal

/-- Theorem 5.3, p. 936: all threshold bounds and optimality on the entire half-line.
The (4.1) hypothesis is inherited from the induction explicitly invoked in the proof. -/
theorem theorem_5_3 {L : ℕ} (D : Data L) (T : ServiceData) (N : ℕ)
    (hD : Standing D) (hT : ServiceFeasible D T N) (h41 : Cond41 D N) :
    ∃ s S : ℕ → Fin L → ℝ,
      (∀ n < N, ∀ i, serviceA D T n i ≤ s n i ∧ s n i ≤ S n i ∧ S n i ≤ T.B) ∧
      (∀ n < N, InB0 (capRule T s S n)) ∧
      (∀ n < N, ∀ i x, x ≤ T.B →
        capAction D T n i x (capRule T s S n i x) ∧
        capV D T N n i x = D.f n i x + orderCost D n i (capRule T s S n i x) +
          F D n (capV D T N (n + 1)) i (x + capRule T s S n i x) ∧
        ∀ u : ℝ, capAction D T n i x u →
          orderCost D n i (capRule T s S n i x) +
              F D n (capV D T N (n + 1)) i (x + capRule T s S n i x) ≤
          orderCost D n i u + F D n (capV D T N (n + 1)) i (x + u)) ∧
      (∀ n ≤ N, ∀ i x, x ≤ T.B →
        CapAdmissible D T N n i x (feedback (capRule T s S) n x) ∧
        0 ≤ capV D T N n i x ∧
        J D N n i x (feedback (capRule T s S) n x) = ENNReal.ofReal (capV D T N n i x) ∧
        capValue D T N n i x = ENNReal.ofReal (capV D T N n i x) ∧
        ∀ U : Policy L, CapAdmissible D T N n i x U →
          J D N n i x (feedback (capRule T s S) n x) ≤ J D N n i x U) := by sorry

end SethiChengSS.Finite.Supplement
