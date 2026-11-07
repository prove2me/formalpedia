-- Prove2me | Theorems.Thm_SecondBestBT_theorem_3_5
-- name    : SecondBestBT.theorem_3_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:48:45.585137+00:00
-- url     : https://prove2.me/theorems/474c082f-0466-4390-9af1-16df619a4c9c
-- title:
--   Theorem 3.5 — exact continuum-to-grid reduction
-- statement:
--   Let $Z_W:=\{0,1,\dots,W\}$. Then
--   $$
--   \inf_{\{(F_S,F_B)\in\Delta([0,1])^2:\ \mathrm{FB}(F_S,F_B)>0\}}\frac{\mathrm{SB}(F_S,F_B)}{\mathrm{FB}(F_S,F_B)}
--   =\inf_{W\ge1}\ \inf_{\{(\hat F_S,\hat F_B)\in\Delta(Z_W)^2:\ \mathrm{FB}(\hat F_S,\hat F_B)>0\}}\frac{\mathrm{SB}(\hat F_S,\hat F_B)}{\mathrm{FB}(\hat F_S,\hat F_B)} .
--   $$
--   On the left $\mathrm{SB}$ has types in $[0,1]$; on the right a prior on $Z_W$ is $\sum_{k\le W}f(k)\delta_k$ for a probability vector $f$, and $\mathrm{SB}$ has types in $[0,W]$.
--
--   The worst-case efficiency ratio over priors on $[0,1]$ is therefore determined by finite integer grids.
--
--   Differences from the source:
--   - reading: $\mathrm{SB}$ for priors on $Z_W$ (the paper evaluates it through the finite program on $Z_W$, the image of the unit grid under scaling by $W$) → the measure-level benchmark with types in $[0,W]$; reason: Section 3 defines SB for types in $[0,1]$ and Theorem 3.5's proof scales $[0,1]$ to $[0,W]$; Corollary 3.2 then identifies it with the finite program
--   - encoding: the infima → `sInf` in $\mathbb R$ of sets of ratios; reason: each set is nonempty ($\delta_0,\delta_1$, resp. $\delta_0,\delta_1$ on $Z_W$) and bounded below by $0$
--   - encoding: mechanisms $(x,p_B,p_S)$ whose integrals are written without conditions → `WellDefined`: Borel measurable rules, $x\in[0,1]$ on $T\times T$, and finite interim-payment, budget-surplus and GFT integrals; reason: the paper's integrals presuppose these conditions; they only shrink the mechanism class, and the paper's constructions satisfy them
--   - encoding: independent priors $F_S,F_B$ supported on a set $A$ → probability measures on $\mathbb R$ with $\mu(\mathbb R\setminus A)=0$; independence is the product measure; reason: same objects
--   - encoding: priors $\hat F_S,\hat F_B\in\Delta(Z_W)$ → probability vectors `f : ℕ → ℝ` with `IsGridPMF f N` (nonnegative, summing to one over the grid indices) and the measures `gridPrior t f N` $=\sum_{i\le N} f(i)\,\delta_{t_i}$; reason: same priors; zero masses are retained, as the paper requires
-- source:
--   Liu–Qin–Ren–Wang, Second-Best Bilateral Trade is 1/2 Efficient, arXiv:2606.03849 (held version, sha256 17184930…), Theorem 3.5, p.7

import Mathlib
import Definitions.Def_SecondBestBT_IsPriorOn
import Definitions.Def_SecondBestBT_secondBest
import Definitions.Def_SecondBestBT_firstBest
import Definitions.Def_SecondBestBT_gridPrior
import Definitions.Def_SecondBestBT_IsGridPMF

open MeasureTheory

namespace SecondBestBT

/-- **Theorem 3.5** (exact continuum-to-grid reduction; Liu–Qin–Ren–Wang, *Second-Best Bilateral
Trade is 1/2 Efficient*, arXiv:2606.03849, held version sha256 17184930…, Theorem 3.5, p.7).
With `Z_W := {0, 1, …, W}`,
`inf_{(F_S,F_B) ∈ ∆([0,1])², FB > 0} SB/FB = inf_{W ≥ 1} inf_{(F̂_S,F̂_B) ∈ ∆(Z_W)², FB > 0} SB/FB`.

**Formalization Note** On the left, priors are probability measures on `[0, 1]` and `SB` has types
in `[0, 1]`. On the right, a prior on `Z_W` is `∑_{k ≤ W} f(k) δ_k` for a probability vector
`f`, and its `SB` has types in `[0, W]`, the image of `[0, 1]` under the scaling by `W` that the
proof uses. Infima are `sInf` in `ℝ` of nonempty sets of nonnegative ratios. -/
theorem theorem_3_5 :
    sInf {r : ℝ | ∃ μS μB : Measure ℝ, IsPriorOn (Set.Icc 0 1) μS ∧
        IsPriorOn (Set.Icc 0 1) μB ∧ 0 < firstBest μS μB ∧
        r = secondBest (Set.Icc 0 1) μS μB / firstBest μS μB} =
      sInf {r : ℝ | ∃ W : ℕ, 1 ≤ W ∧
        r = sInf {r' : ℝ | ∃ fS fB : ℕ → ℝ, IsGridPMF fS W ∧ IsGridPMF fB W ∧
          0 < firstBest (gridPrior (fun k => (k : ℝ)) fS W) (gridPrior (fun k => (k : ℝ)) fB W) ∧
          r' = secondBest (Set.Icc 0 W) (gridPrior (fun k => (k : ℝ)) fS W)
              (gridPrior (fun k => (k : ℝ)) fB W) /
            firstBest (gridPrior (fun k => (k : ℝ)) fS W) (gridPrior (fun k => (k : ℝ)) fB W)}} := by sorry

end SecondBestBT
