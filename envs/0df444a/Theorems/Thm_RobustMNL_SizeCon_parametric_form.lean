-- Prove2me | Theorems.Thm_RobustMNL_SizeCon_parametric_form
-- name    : RobustMNL.SizeCon.parametric_form
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-07T14:21:21.309166+00:00
-- url     : https://prove2.me/theorems/ffb743d4-abad-49e0-a6ef-42001713dd31
-- title:
--   Proof of Theorem 3.8, p. 12 — Y*(V) = max{λ : max_{|S|≤K} min_{v∈V} (1/v₀) Σ_{i∈S} v_i (r_i − λ) ≥ λ}
-- statement:
--   Let $\mathcal V\subseteq\mathbb R^{n+1}_{++}$ be a compact, nonempty set of positive MNL parameter vectors $v=(v_0,v_1,\dots,v_n)$, let $r_1,\dots,r_n$ be real revenues and $K\in\mathbb N$ a size limit. Write $Y^*(\mathcal V)=\max_{S\subseteq\mathcal A:\,|S|\le K}\min_{v\in\mathcal V} f(S,v)$ for the optimal value of the size-constrained robust problem. Then $Y^*(\mathcal V)$ is the **largest** real number $\lambda$ satisfying
--
--   $$
--   \max_{S:\ |S|\le K}\ \min_{v\in\mathcal V}\ \frac{1}{v_0}\sum_{i\in S} v_i\,(r_i-\lambda)\ \ge\ \lambda ,
--   $$
--
--   that is,
--
--   $$
--   Y^*(\mathcal V)=\max\Big\{\lambda:\ \max_{S:\ |S|\le K}\ \min_{v\in\mathcal V}\ \frac{1}{v_0}\sum_{i\in S} v_i\,(r_i-\lambda)\ \ge\ \lambda\Big\}.
--   $$
--
--   This parametric (Dinkelbach-type) description of $Y^*$ holds for every compact uncertainty set; it is the first step of the proof of Theorem 3.8, which then evaluates the left-hand side in closed form when $\mathcal V$ is a box.
--
--   **Formalization Note** The "max" of the set of admissible $\lambda$ is `IsGreatest`: $Y^*(\mathcal V)$ belongs to the set and bounds every member, so the maximum is attained. The inner $\min$ is a real infimum over $\mathcal V$, attained under the stated hypotheses (compact, nonempty, every component positive). Revenues are arbitrary reals; the paper's ordering $r_1\ge\dots\ge r_n>0$ is not assumed. Products are 0-indexed (`Fin n`).
-- source:
--   Rusmevichientong, Topaloglu, Robust Assortment Optimization in Revenue Management Under the Multinomial Logit Choice Model, Operations Research (2012), doi:10.1287/opre.1120.1063, authors' manuscript of 20 Sep 2011, proof of Theorem 3.8, p. 12, first display (last line)

import Mathlib
import Definitions.Def_ChoiceCDLP_MNL_mnlObjective
import Definitions.Def_RobustMNL_SizeCon_Model

namespace RobustMNL.SizeCon

/-- Proof of Theorem 3.8, p. 12, first display: for every compact, nonempty uncertainty set
`V ⊆ ℝⁿ⁺¹₊₊`, `Y*(V)` is the largest `λ` with
`λ ≤ max_{S : |S| ≤ K} min_{v ∈ V} (1/v₀) ∑_{i ∈ S} v_i (r_i − λ)`. -/
theorem parametric_form {n : ℕ} (V : Set (ℝ × (Fin n → ℝ))) (hVc : IsCompact V)
    (hVne : V.Nonempty) (hVpos : ∀ p ∈ V, RobustMNL.Static.IsPos p) (r : Fin n → ℝ) (K : ℕ) :
    IsGreatest {lam : ℝ | lam ≤ paramValue V r K lam} (Ystar V r K) := by sorry

end RobustMNL.SizeCon
