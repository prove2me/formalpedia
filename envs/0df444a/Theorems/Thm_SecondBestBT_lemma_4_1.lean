-- Prove2me | Theorems.Thm_SecondBestBT_lemma_4_1
-- name    : SecondBestBT.lemma_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:49:40.912957+00:00
-- url     : https://prove2.me/theorems/f1459788-caa8-4789-92eb-1265b80d307d
-- title:
--   Lemma 4.1 — minimax (Lagrangian) representation of the second-best benchmark
-- statement:
--   Let $f_S,f_B$ be priors on the integer grid $Z_W=\{0,\dots,W\}$, zero masses retained. The second-best benchmark admits the minimax representation
--   $$
--   \mathrm{SB}_{F_S,F_B}=\inf_{\alpha\ge0}\ \sup_{x\in R_1(W)}\big[\mathrm{GFT}(x)+\alpha\,\Lambda_D(x)\big],
--   $$
--   where $\mathrm{SB}$ is the measure-level benchmark of the priors $\sum_k f_S(k)\delta_k$, $\sum_k f_B(k)\delta_k$ with types in $[0,W]$, and $\mathrm{GFT}$, $\Lambda_D$, $R_1(W)$ are those of the integer grid.
--
--   The lemma removes the budget constraint from the allocation domain by dualizing it with a multiplier $\alpha$.
--
--   Differences from the source:
--   - reading: $\mathrm{SB}$ for priors on $Z_W$ (the paper evaluates it through the finite program on $Z_W$, the image of the unit grid under scaling by $W$) → the measure-level benchmark with types in $[0,W]$; reason: Section 3 defines SB for types in $[0,1]$ and Theorem 3.5's proof scales $[0,1]$ to $[0,W]$; Corollary 3.2 then identifies it with the finite program
--   - encoding: $\inf_{\alpha\ge0}$ and $\sup_{x\in R_1(W)}$ → `sInf` over $\alpha\in[0,\infty)$ of `sSup` over $R_1(W)$; reason: each inner set is nonempty and bounded (finite cube), and every inner value is $\ge0$ (zero allocation)
--   - encoding: allocations $x:Z_W^2\to[0,1]$ → matrices `ℕ → ℕ → ℝ` constrained and evaluated only at indices $\le W$; reason: entries above $W$ enter no sum and no constraint
--   - encoding: mechanisms $(x,p_B,p_S)$ whose integrals are written without conditions → `WellDefined`: Borel measurable rules, $x\in[0,1]$ on $T\times T$, and finite interim-payment, budget-surplus and GFT integrals; reason: the paper's integrals presuppose these conditions; they only shrink the mechanism class, and the paper's constructions satisfy them
--   - encoding: priors $F_S,F_B\in\Delta(Z_W)$ → probability vectors `f : ℕ → ℝ` with `IsGridPMF f N` (nonnegative, summing to one over the grid indices) and the measures `gridPrior t f N` $=\sum_{i\le N} f(i)\,\delta_{t_i}$; reason: same priors; zero masses are retained, as the paper requires
-- source:
--   Liu–Qin–Ren–Wang, Second-Best Bilateral Trade is 1/2 Efficient, arXiv:2606.03849 (held version, sha256 17184930…), Lemma 4.1, p.8

import Mathlib
import Definitions.Def_SecondBestBT_secondBest
import Definitions.Def_SecondBestBT_gridPrior
import Definitions.Def_SecondBestBT_IsGridPMF
import Definitions.Def_SecondBestBT_gftZ
import Definitions.Def_SecondBestBT_lambdaZ
import Definitions.Def_SecondBestBT_R1

open MeasureTheory

namespace SecondBestBT

/-- **Lemma 4.1** (minimax representation; Liu–Qin–Ren–Wang, *Second-Best Bilateral Trade is 1/2
Efficient*, arXiv:2606.03849, held version sha256 17184930…, Lemma 4.1, p.8). For priors
`f_S, f_B ∈ ∆(Z_W)` on the integer grid `Z_W = {0, …, W}` (zero masses retained), the
second-best benchmark admits the representation
`SB_{F_S,F_B} = inf_{α ≥ 0} sup_{x ∈ R1(W)} [GFT(x) + α Λ_D(x)]`.

**Formalization Note** The left side is the measure-level benchmark `secondBest` of the priors
`∑_k f(k) δ_k`, with types in `[0, W]` (the scaled image of the unit interval of Section 3), not
the value of the finite program. The `sup` is `sSup` over the nonempty, bounded set of values on
`R1(W)`; the `inf` is `sInf` over `α ∈ [0, ∞)` of values that are at least `0` (the zero
allocation). -/
theorem lemma_4_1 (W : ℕ) (fS fB : ℕ → ℝ) (hfS : IsGridPMF fS W) (hfB : IsGridPMF fB W) :
    secondBest (Set.Icc 0 (W : ℝ)) (gridPrior (fun k => (k : ℝ)) fS W)
        (gridPrior (fun k => (k : ℝ)) fB W) =
      sInf ((fun α : ℝ => sSup ((fun x => gftZ fS fB W x + α * lambdaZ fS fB W x) ''
        R1 fS fB W)) '' Set.Ici 0) := by sorry

end SecondBestBT
