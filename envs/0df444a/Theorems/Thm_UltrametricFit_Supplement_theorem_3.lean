-- Prove2me | Theorems.Thm_UltrametricFit_Supplement_theorem_3
-- name    : UltrametricFit.Supplement.theorem_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T01:21:57.539918+00:00
-- url     : https://prove2.me/theorems/f11897a2-6f26-4624-b6b7-3d105736dc10
-- title:
--   Theorem 3, p.2 — Merge rounding is a $12.091$-approximation for $\ell_1$-Ultrametric Fitting
-- statement:
--   Theorem 3 gives an explicit constant for the $\ell_1$ objective: Merge rounding of the standard LP is a $12.091$-approximation. The algorithm solves the LP for $p=1$ and runs Algorithm 1, Merge($\delta$), with
--   $$\delta=\frac{3-\sqrt5}{4}.$$
--
--   For every $n$ and every instance $X:\binom{[n]}{2}\to\mathbb R_{>0}$:
--
--   1. the LP for $p=1$ has an optimal solution;
--   2. each feasible point of the LP admits a run of Merge($\delta$);
--   3. each run of Merge($\delta$) on each optimal solution for $p=1$ has an output;
--   4. each output $U$ of such a run is an ultrametric and, for every ultrametric $U'$,
--   $$\|U-X\|_1=\sum_{i<j}|U(i,j)-X(i,j)|\le 12.091\cdot\|U'-X\|_1.$$
--
--   The bound holds for every merge order and against every ultrametric, not only those with values among the input distances. At $p=1$ the main theorem gives only an unspecified constant; this result names one, improving the previous best factor for $\ell_1$-Ultrametric Fitting.
--
--   Differences from the source:
--   - reading: "there exists a 12.091-approximation" → the guarantee for the algorithm of the proof (§4.5): an optimal LP solution for $p=1$, then Merge($\delta$) with $\delta=(3-\sqrt5)/4$, for every optimal solution, every run and every output; no machine and no running-time clause; reason: the paper's existence claim is proved by this algorithm (pp.15–16) and it analyses no running time; a bare existence of a good ultrametric would be trivially true
--   - generalization: the LP optimum and an execution of the algorithm are taken as given → also: an optimum exists, every feasible point admits a run, every run on an optimal solution has an output, and every output is an ultrametric; reason: these make the guarantee non-vacuous and are the §3 facts about the algorithm; dropping them leaves the bound
--   - encoding: Algorithm 1, Merge($\delta$), with unspecified merge order → the published relation `IsRun` (every merge order) and the relational output `IsOutput`; reason: the paper fixes no order, so every order is an execution of the algorithm; §5 speaks of the worst one
--   - encoding: $X, U, x_\ell$ are functions on unordered pairs → symmetric functions on `Fin n × Fin n` (the published base definitions), with sums over $i<j$ and diagonals never read; reason: Lean convention of the base mission; same instances
--   - encoding: the constant 12.091 → the real number `12091 / 1000`; reason: the printed decimal, exactly
-- source:
--   Charikar, Gao, Fitting Ultrametrics under any ℓ_p Objective, STOC 2027 submission (manuscript sha256 87af12a2…), Theorem 3, p.2 (PDF p.3); proof §4.5, pp.15–16 (PDF pp.16–17); algorithm: Algorithm 1, p.8

import Mathlib
import Definitions.Def_UltrametricFit_IsInstance
import Definitions.Def_UltrametricFit_IsFeasible
import Definitions.Def_UltrametricFit_IsRun

namespace UltrametricFit.Supplement

open UltrametricFit

/-- **Theorem 3**, Charikar, Gao, *Fitting Ultrametrics under any ℓ_p Objective*, STOC 2027
submission (manuscript sha256 87af12a2…), p.2: "There exists a 12.091-approximation for the
ℓ1-Ultrametric Fitting problem." Proof in §4.5, pp.15–16: an optimal solution of the LP for `p = 1`,
then Merge(δ) (Algorithm 1, p.8) with `δ = (3 − √5)/4`.

For every instance: the LP for `p = 1` has an optimal solution; each feasible point admits a run of
Merge((3 − √5)/4); and each run on each optimal solution has an output, and each of its outputs is
an ultrametric `U` with `‖U − X‖₁ ≤ 12.091 · ‖U′ − X‖₁` for every ultrametric `U′`.

**Formalization Note.** Every merge order and every output are covered. `12.091` is the real
`12091 / 1000`. `lpDist 1` is `Σ_{i<j} |U(i, j) − X(i, j)|`. Optimality is for the `ℓ1` objective
(`IsOptimal X 1`). No running time is stated: the paper analyses none. -/
theorem theorem_3 :
    ∀ (n : ℕ) (X : Fin n → Fin n → ℝ), IsInstance X →
      (∃ x, IsOptimal X 1 x) ∧
      (∀ x, IsFeasible X x → ∃ Cl M, IsRun X x ((3 - Real.sqrt 5) / 4) Cl M) ∧
      ∀ x, IsOptimal X 1 x → ∀ Cl M, IsRun X x ((3 - Real.sqrt 5) / 4) Cl M →
        (∃ U, IsOutput X Cl U) ∧
        ∀ U, IsOutput X Cl U →
          IsUltrametric U ∧
          ∀ U', IsUltrametric U' → lpDist 1 U X ≤ 12091 / 1000 * lpDist 1 U' X := by sorry

end UltrametricFit.Supplement
