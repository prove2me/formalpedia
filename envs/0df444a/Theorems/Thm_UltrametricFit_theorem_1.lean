-- Prove2me | Theorems.Thm_UltrametricFit_theorem_1
-- name    : UltrametricFit.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:45:50.749655+00:00
-- url     : https://prove2.me/theorems/5d89a880-3724-47ad-a034-2611c5ac2cb0
-- title:
--   Theorem 1, p.2 — merge rounding of the standard LP is an $O(p)$-approximation
-- statement:
--   This is the main theorem of the paper: for every $p>1$ there is an $O(p)$-approximation for $\ell_p$-Ultrametric Fitting, namely an optimal solution of the standard LP rounded by Algorithm 1, Merge($\delta$), for a constant $\delta\in(0,0.5)$.
--
--   For each $\delta\in(0,1/2)$ there is a constant $C>0$, chosen before $p$, $n$ and $X$, such that for every real $p\ge1$, every $n$ and every instance $X:\binom{[n]}{2}\to\mathbb R_{>0}$:
--
--   1. the LP has an optimal solution;
--   2. each feasible point of the LP admits a run of Merge($\delta$);
--   3. each run of Merge($\delta$) on each optimal solution performs exactly $n-1$ merges and ends with the single cluster $[n]$ (for $n\ge1$), and it has an output;
--   4. each output $U$ of such a run is an ultrametric with values in $\{D_1,\dots,D_L\}$ and, for every ultrametric $U'$,
--   $$\|U-X\|_p\le C\,p\,\|U'-X\|_p.$$
--
--   The bound holds for every merge order and against every ultrametric, not only those with values among the $D_\ell$. It is the first constant-factor approximation for any fixed $p>1$.
--
--   Differences from the source:
--   - reading: "there exists an $O(p)$-approximation" → the guarantee for the paper's algorithm (LP optimum, then Merge($\delta$), every optimal solution and every run), with no machine and no running-time clause; reason: the paper's existence claim is proved by this algorithm and it analyses no running time; a bare existence of a good ultrametric would be trivially true, since a minimizer among the finitely many $D$-valued ultrametrics is within factor 2 by Lemma 4
--   - generalization: $p>1$ in the theorem → every real $p\ge1$; reason: the sentence introducing the theorem (p.1), §2 (p.6) and the closing remark of the proof (p.15) include $p=1$; restricting to $p>1$ gives the printed case
--   - generalization: a constant $\delta\in(0,0.5)$ → every $\delta\in(0,1/2)$, with $C$ depending on $\delta$; reason: p.15 says $\Gamma=O(p)$ for any constant $\delta$; any single constant is an instance
--   - generalization: the LP optimum and an execution of the algorithm are taken as given → also: an optimum exists, runs exist on feasible points, each run performs $n-1$ merges, ends with one cluster and has an output, and the output is an ultrametric with values in the $D_\ell$; reason: these make the guarantee non-vacuous and are the §3 facts about the algorithm; dropping them leaves the bound
--   - encoding: Algorithm 1 with unspecified merge order → a relation `IsRun` with a universal quantifier over runs, and a relational output `IsOutput`; reason: the paper fixes no order (and §5 speaks of the worst one), so every order is an execution of the algorithm
--   - encoding: $X, U, x_\ell$ are functions on unordered pairs → symmetric functions on `Fin n × Fin n`, with sums over $i<j$ and diagonals never read; reason: Lean convention; same instances
-- source:
--   Charikar, Gao, Fitting Ultrametrics under any ℓ_p Objective, STOC 2027 submission (manuscript sha256 87af12a2…), Theorem 1, p.2 (PDF p.3); algorithm: Algorithm 1 and §3, p.8; p ≥ 1: p.1 and §2, p.6

import Mathlib
import Definitions.Def_UltrametricFit_IsInstance
import Definitions.Def_UltrametricFit_IsFeasible
import Definitions.Def_UltrametricFit_IsRun

namespace UltrametricFit

/-- **Theorem 1**, Charikar, Gao, *Fitting Ultrametrics under any ℓ_p Objective*, STOC 2027 submission
(manuscript sha256 87af12a2…), p.2: "For any p > 1, there exists an O(p)-approximation for the
ℓp-Ultrametric Fitting problem." The approximation is the paper's algorithm: an optimal solution of
(ℓp-ultrametric-LP), then Merge(δ) (Algorithm 1, p.8), for a constant `δ ∈ (0, 0.5)`.

For every `δ ∈ (0, 1/2)` there is a `C > 0`, chosen before `p`, `n` and `X`, such that for every
real `p ≥ 1` and every instance: the LP has an optimal solution; each feasible point admits a run;
and each run on each optimal solution performs `n − 1` merges, ends with one cluster, has an output,
and each of its outputs is an ultrametric with values in `{D_1, …, D_L}` within factor `C · p` of
every ultrametric.

**Formalization Note.** Every merge order is covered. `n − 1` merges is written `+ 1 = n` under
`0 < n`, to avoid natural-number subtraction. No machine and no running time are stated: the paper
analyses none. The theorem prints `p > 1`, while the sentence introducing it (p.1) and §2 (p.6) have
`p ≥ 1`. -/
theorem theorem_1 :
    ∀ δ : ℝ, 0 < δ → δ < 1 / 2 → ∃ C : ℝ, 0 < C ∧
      ∀ p : ℝ, 1 ≤ p → ∀ (n : ℕ) (X : Fin n → Fin n → ℝ), IsInstance X →
        (∃ x, IsOptimal X p x) ∧
        (∀ x, IsFeasible X x → ∃ Cl M, IsRun X x δ Cl M) ∧
        ∀ x, IsOptimal X p x → ∀ Cl M, IsRun X x δ Cl M →
          (0 < n → (mergeEvents X M).length + 1 = n ∧ Cl (numLayers X) = {Finset.univ}) ∧
          (∃ U, IsOutput X Cl U) ∧
          ∀ U, IsOutput X Cl U →
            IsUltrametric U ∧
            (∀ i j, i ≠ j → ∃ ℓ ∈ Finset.Icc 1 (numLayers X), U i j = layerValue X ℓ) ∧
            ∀ U', IsUltrametric U' → lpDist p U X ≤ C * p * lpDist p U' X := by sorry

end UltrametricFit
