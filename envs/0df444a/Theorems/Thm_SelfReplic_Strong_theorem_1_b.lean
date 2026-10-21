-- Prove2me | Theorems.Thm_SelfReplic_Strong_theorem_1_b
-- name    : SelfReplic.Strong.theorem_1_b
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-10-21T03:25:18.187427+00:00
-- url     : https://prove2.me/theorems/06d25979-3f38-4060-bc52-10b43a0f6d86
-- title:
--   Theorem 1(b), p. 10 — under Strong Replicability, if I̲ < I_L < Ī the optimal policy keeps sales on and switches production on once, depleting inventory exactly at T
-- statement:
--   Consider the base model of Hu and Sun under the standing assumptions, and assume Strong Replicability
--   $$(r-\rho)\pi>cr+h.$$
--   Let $\underline I$ be a level of the launch inventory at which always keeping production and sales on ($p=rI$, $s=d$) depletes the inventory exactly at $T$. Let $\overline I$ be a level at which always keeping production off and sales on ($p=0$, $s=d$) depletes the inventory exactly at $T$. All other parameters are unchanged.
--
--   **Case (b).** If $\underline I<I_L<\overline I$, there are a time $t_p\in[0,T]$ and an optimal trajectory with sales always on ($s=d$ on $[0,T]$) and production off before $t_p$ and on from $t_p$ ($p=0$ on $[0,t_p)$, $p=rI$ on $[t_p,T]$), whose inventory is depleted exactly at $T$.
--
--   Here "optimal" means
--   $$\int_0^T\big[\pi s-cp-hI\big]e^{-\rho t}\,dt\;\ge\;\int_0^T\big[\pi \tilde s-c\tilde p-h\tilde I\big]e^{-\rho t}\,dt$$
--   for every admissible trajectory $(\tilde D,\tilde S,\tilde I,\tilde p,\tilde s)$ with the same parameters. "Depleted exactly at $T$" means $I(T)=0$ and $I(t)>0$ for $0\le t<T$.
--
--   This is one of the three cases of the paper's main result, Theorem 1. The three cases together are the goal theorem `SelfReplic.Strong.theorem_1`.
--
--   **Formalization Note** The binders are exactly those of `SelfReplic.Strong.theorem_1`, and the conclusion is its corresponding conjunct. The competitor ranges over all admissible trajectories, not only over policies of the stated shape. The thresholds are real numbers given with their defining property.
-- source:
--   Hu & Sun, Managing self-replicating innovative goods, authors' manuscript of 2020-10-18 (Management Science, doi:10.1287/mnsc.2020.3936), p. 10, Theorem 1(b) (proof pp. 36–37)

import Mathlib
import Definitions.Def_SelfReplic_Strong_Model

namespace SelfReplic.Strong

/-- Theorem 1(b) (Strong Replicability), p. 10: if `I̲ < I_L < Ī`, a trajectory with sales always on
and production switched on once at `tp`, depleting the inventory exactly at `T`, is optimal. -/
theorem theorem_1_b (P : Params) (hP : P.Standing) (hSR : P.StrongRepl)
    (Ilow Ihigh : ℝ) (hlow : IsLowLevel P Ilow) (hhigh : IsHighLevel P Ihigh) :
    Ilow < P.IL → P.IL < Ihigh → ∃ tp ∈ Set.Icc 0 P.T, ∃ x : Traj,
        IsOptimal P x ∧ SalesAlwaysOn P x ∧ ProdOnFrom P x tp ∧ DepletedExactlyAtT P x := by sorry

end SelfReplic.Strong
