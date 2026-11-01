-- Prove2me | Theorems.Thm_PWDB_remark_C_1
-- name    : PWDB.remark_C_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:38:57.492823+00:00
-- url     : https://prove2.me/theorems/efb07222-fd2c-482d-b8ed-6bed6f65a78f
-- title:
--   Remark C.1 — strict inequalities do not change the infimum of (P)
-- statement:
--   Let $E$ be a finite-dimensional real inner product space, $I$ a finite index set, and $f_0, f_i : E \to \overline{\mathbb R}$ ($i \in I$) satisfy assumption (F): each $f_i$, $i \in I_0 = \{0\} \cup I$, is proper, closed and convex.
--
--   Let $x^S$ be a strict Slater point of (P). Then:
--
--   1. for every feasible $x$ of (P) and every integer $n \ge 1$, the point $x_n = \tfrac1n x^S + (1 - \tfrac1n) x$ is a strict Slater point of (P);
--   2. $x_n \to x$;
--   3. $f_0(x) = \liminf_{n\to\infty} f_0(x_n)$;
--   4. $\inf\{f_0(x) \mid f_i(x) < 0\ \forall i \in I\} = \inf(\mathrm P)$.
--
--   Replacing the weak inequalities of (P) by strict ones therefore leaves its infimum unchanged.
--
--   Differences from the source:
--   - generalization: ℝ^{dx}, ℝ^{dz} → finite-dimensional real inner product spaces E, F; reason: every ℝ^d with the dot product is such a space, so the Lean statement specializes to the printed one
--   - encoding: (F): fi proper, closed and convex, values in R̄ → TensorAHPE.IsProperClosedConvex (never −∞, somewhere finite, lower semicontinuous, convex epigraph), values in EReal; reason: for a proper function the paper's 'closed' (p.39) is lower semicontinuity; same instances
--   - encoding: optimal values, feasible regions and solvability of p.40 → EReal ⨅/⨆ over the feasible region; feasibility excludes the bad objective value; Solvable includes the infeasible case; reason: Lean transcription of the conventions stated on p.40; same instances
--   - encoding: n ∈ ℕ in xn = (1/n)xS + (1 − 1/n)x → n : ℕ with 1 ≤ n in clause 1; the limit and lim inf along atTop; reason: the sequence is indexed by positive integers; in Lean 1/0 = 0 would give x0 = x, which is not a Slater point; the limit and lim inf do not see finitely many terms
--   - encoding: index sets I, I0 = {0} ∪ I → Fintype ι (possibly empty), with the index 0 carried separately as f₀, w₀; reason: Lean convention; same instances
-- source:
--   Zhen, Kuhn & Wiesemann, A Unified Theory of Robust and Distributionally Robust Optimization via the Primal-Worst-Equals-Dual-Best Principle, arXiv:2105.00760v2 (19 Jul 2023), Remark C.1, p.68

import Mathlib
import Definitions.Def_TensorAHPE_IsProperClosedConvex
import Definitions.Def_PWDB_ConvexProgram
import Definitions.Def_PWDB_Slater

open Filter Topology

namespace PWDB

/-- **Remark C.1 (Strict Inequalities)** (Zhen, Kuhn & Wiesemann, arXiv:2105.00760v2, Remark C.1,
p.68): "If (P) admits a strict Slater point `xS`, then any feasible solution `x` of (P) can be
expressed as the limit of a sequence of strict Slater points `xn = (1/n)xS + (1 − 1/n)x`, `n ∈ ℕ`,
and its objective function value satisfies `f0(x) = lim inf_{n→∞} f0(xn)`. […] Therefore,
replacing weak inequalities by strict inequalities in (P) does not change the infimum of (P) if
(P) admits a strict Slater point."

Under (F), with `xS` a strict Slater point of (P):
1. for every feasible `x` of (P) and every `n ≥ 1`, `xn` is a strict Slater point of (P);
2. `xn → x`;
3. `f0(x) = lim inf f0(xn)`;
4. `inf {f0(x) | fi(x) < 0 ∀i ∈ I} = inf (P)`.

**Formalization Note** `n` ranges over `ℕ` with `n ≥ 1` in clause 1 (at `n = 0` Lean's `1/0 = 0`
would give `x0 = x`); clauses 2 and 3 concern the tail of the sequence only. A strict Slater point
is `StrictSlaterMin` (Definition 2) with no equality constraints. A feasible solution is a point
of `pFeas` (p.40). The `lim inf` and the infima are taken in `EReal`. -/
theorem remark_C_1 {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [Fintype ι]
    (f₀ : E → EReal) (f : ι → E → EReal)
    (hf₀ : TensorAHPE.IsProperClosedConvex f₀) (hf : ∀ i, TensorAHPE.IsProperClosedConvex (f i))
    (xS : E) (hxS : StrictSlaterMin f₀ f (fun e : Empty => e.elim) xS) :
    (∀ x ∈ pFeas f₀ f,
      (∀ n : ℕ, 1 ≤ n →
        StrictSlaterMin f₀ f (fun e : Empty => e.elim)
          ((1 / (n : ℝ)) • xS + (1 - 1 / (n : ℝ)) • x)) ∧
      Tendsto (fun n : ℕ => (1 / (n : ℝ)) • xS + (1 - 1 / (n : ℝ)) • x) atTop (𝓝 x) ∧
      f₀ x = liminf (fun n : ℕ => f₀ ((1 / (n : ℝ)) • xS + (1 - 1 / (n : ℝ)) • x)) atTop) ∧
    (⨅ x ∈ {x : E | ∀ i, f i x < 0}, f₀ x) = pVal f₀ f := by sorry

end PWDB
