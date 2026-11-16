-- Prove2me | Theorems.Thm_UltrametricFit_Supplement_theorem_16
-- name    : UltrametricFit.Supplement.theorem_16
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T01:22:47.522105+00:00
-- url     : https://prove2.me/theorems/4672270e-9390-433f-b027-b9bc81d62087
-- title:
--   Theorem 16, p.17 — the analysis of Merge($\delta$) cannot beat $B=6.08155648$
-- statement:
--   Let $C(\delta)$ be the worst-case ratio of the $\ell_1$ error of Merge($\delta$) to the $\ell_1$ LP cost, over all instances, all feasible LP points with positive cost, all merge orders and all outputs, and let
--   $$B=\frac{2375608}{390625}=6.08155648.$$
--   Then for every $\delta>0$,
--   $$C(\delta)\ge B.$$
--
--   Equivalently, for every $b<B$ there are an instance $X$, a feasible point $x$ with $\text{lp-cost}_1(x)>0$, a run of Merge($\delta$) on $x$ and an output $U$ of it with $\|U-X\|_1>b\cdot\text{lp-cost}_1(x)$. The supremum need not be attained.
--
--   No choice of the threshold $\delta$ lets an analysis that compares Merge($\delta$) to the LP cost pair by pair, under the worst merge order, prove a factor below $6.08$ for $\ell_1$-Ultrametric Fitting, even on Correlation Clustering instances.
--
--   Differences from the source:
--   - encoding: $C(\delta)$, "the supremum over all instances and feasible LP solutions x of the ℓ1 error of the solution produced by the Merge(δ)) algorithm divided by lp-costp(x)" → `mergeRatioSup δ : EReal`, the supremum over $n$, instances $X$, feasible $x$, runs $(Cl,M)$ of Merge($\delta$) and outputs $U$ of $\|U-X\|_1/\text{lp-cost}_1(x)$; reason: the worst merge order (p.16) is a supremum over runs; `EReal` represents the value $\infty$ of Lemma 18 and has no junk supremum
--   - encoding: the ratio $\|U-X\|_1/\text{lp-cost}_1(x)$ → taken only where $\text{lp-cost}_1(x)>0$; reason: the ratio is undefined at a zero denominator (Lemma 15 assumes cost$_w(x)>0$); only undefined cases are excluded, and excluding them can only lower the supremum, so the bound is not weakened
--   - encoding: Algorithm 1, Merge($\delta$), with unspecified merge order → the published relation `IsRun` (every merge order) and the relational output `IsOutput`; reason: the paper fixes no order, so every order is an execution of the algorithm; §5 speaks of the worst one
--   - encoding: $X, U, x_\ell$ are functions on unordered pairs → symmetric functions on `Fin n × Fin n` (the published base definitions), with sums over $i<j$ and diagonals never read; reason: Lean convention of the base mission; same instances
--   - encoding: $B=2375608/390625=6.08155648$ → the real `2375608 / 390625`, cast to `EReal`; reason: the exact rational of §5.2
-- source:
--   Charikar, Gao, Fitting Ultrametrics under any ℓ_p Objective, STOC 2027 submission (manuscript sha256 87af12a2…), Theorem 16, p.17 (PDF p.18); B: §5.2, p.17; C(δ): §5, p.16; proof §5.9.1, p.28 (PDF p.29)

import Mathlib
import Definitions.Def_UltrametricFit_Supplement_mergeRatioSup

namespace UltrametricFit.Supplement

/-- **Theorem 16**, Charikar, Gao, *Fitting Ultrametrics under any ℓ_p Objective*, STOC 2027
submission (manuscript sha256 87af12a2…), p.17: "For every δ > 0 we have C(δ) ≥ B", where
`B = 2375608/390625 = 6.08155648` (§5.2, p.17) and `C(δ)` is the worst-case ratio of Merge(δ)
against the `ℓ1` LP cost (§5, p.16; `mergeRatioSup`). Proof on p.28.

**Formalization Note.** `B` is the exact rational `2375608 / 390625`. `δ` ranges over all positive
reals, including `δ ≥ 1/2`, where the page has `C(δ) = ∞`. The inequality is between extended
reals: it says that for every `b < B` some instance, feasible point with positive `ℓ1` LP cost, run
and output have ratio `> b`; the supremum need not be attained. -/
theorem theorem_16 :
    ∀ δ : ℝ, 0 < δ → (((2375608 : ℝ) / 390625 : ℝ) : EReal) ≤ mergeRatioSup δ := by sorry

end UltrametricFit.Supplement
