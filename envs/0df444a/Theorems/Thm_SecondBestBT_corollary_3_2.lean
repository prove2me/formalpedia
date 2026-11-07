-- Prove2me | Theorems.Thm_SecondBestBT_corollary_3_2
-- name    : SecondBestBT.corollary_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:48:45.952692+00:00
-- url     : https://prove2.me/theorems/09b037b2-96a8-4ece-8f17-6767d5becb55
-- title:
--   Corollary 3.2 — the second-best benchmark on a finite grid is a finite program
-- statement:
--   Let $D=\{0=t_0<t_1<\dots<t_N=1\}$ be a finite grid, and let the seller and buyer priors put masses $f_S(i)$, $f_B(j)$ on its points, zero masses allowed. Then the second-best benchmark $\mathrm{SB}$ (types in $[0,1]$) of the priors $\sum_i f_S(i)\delta_{t_i}$ and $\sum_j f_B(j)\delta_{t_j}$ is the **maximum** of
--   $$
--   \sum_{i,j=0}^{N}(t_j-t_i)\,x(i,j)\,f_S(i)\,f_B(j)
--   $$
--   over matrices $x\in[0,1]^{(N+1)^2}$ for which $(x_B(j))_j$ is weakly increasing, $(x_S(i))_i$ is weakly decreasing, and $\Lambda^D_D(x)\ge0$. All seller and buyer grid points are retained, including those with zero mass.
--
--   This turns the second-best problem for grid priors into a finite-dimensional linear program.
--
--   Differences from the source:
--   - encoding: the maximum of the finite program equals SB → `IsGreatest` of the set of feasible values, at the value `secondBest`; reason: the maximum is attained and bounds every value: exactly `IsGreatest`
--   - encoding: the grid $D=\{0=t_0<\dots<t_N=1\}$ → a sequence `t : ℕ → ℝ` with $t_0=0$, $t_N=1$ and $t_i<t_{i+1}$ for $i<N$; reason: same grids; values beyond $N$ are unused
--   - encoding: mechanisms $(x,p_B,p_S)$ whose integrals are written without conditions → `WellDefined`: Borel measurable rules, $x\in[0,1]$ on $T\times T$, and finite interim-payment, budget-surplus and GFT integrals; reason: the paper's integrals presuppose these conditions; they only shrink the mechanism class, and the paper's constructions satisfy them
--   - encoding: independent priors $F_S,F_B$ supported on a set $A$ → probability measures on $\mathbb R$ with $\mu(\mathbb R\setminus A)=0$; independence is the product measure; reason: same objects
--   - encoding: priors supported on the grid $D$ with masses $f_S(i),f_B(j)$ → probability vectors `f : ℕ → ℝ` with `IsGridPMF f N` (nonnegative, summing to one over the grid indices) and the measures `gridPrior t f N` $=\sum_{i\le N} f(i)\,\delta_{t_i}$; reason: same priors; zero masses are retained, as the paper requires
-- source:
--   Liu–Qin–Ren–Wang, Second-Best Bilateral Trade is 1/2 Efficient, arXiv:2606.03849 (held version, sha256 17184930…), Corollary 3.2, p.6

import Mathlib
import Definitions.Def_SecondBestBT_secondBest
import Definitions.Def_SecondBestBT_gridPrior
import Definitions.Def_SecondBestBT_IsGridPMF
import Definitions.Def_SecondBestBT_IsGridFeasible
import Definitions.Def_SecondBestBT_gridGFT

open MeasureTheory

namespace SecondBestBT

/-- **Corollary 3.2** (Liu–Qin–Ren–Wang, *Second-Best Bilateral Trade is 1/2 Efficient*,
arXiv:2606.03849, held version sha256 17184930…, Corollary 3.2, p.6). Let
`D = {0 = t_0 < ⋯ < t_N = 1}` be a finite grid and let the priors put masses `f_S(i)`, `f_B(j)`
on its points (zero masses allowed). Then the second-best benchmark (types in `[0, 1]`) is the
**maximum** of `∑_{i,j} (t_j − t_i) x(i, j) f_S(i) f_B(j)` over matrices in `[0, 1]^{(N+1)²}`
with `(x_B(j))_j` weakly increasing, `(x_S(i))_i` weakly decreasing and `Λ^D_D(x) ≥ 0`.

**Formalization Note** "Maximum" is `IsGreatest`: the value `SB` is attained by a feasible grid
matrix and bounds every such value. All `N + 1` grid points are retained. -/
theorem corollary_3_2 (N : ℕ) (t : ℕ → ℝ) (ht0 : t 0 = 0) (htN : t N = 1)
    (ht : ∀ i < N, t i < t (i + 1)) (fS fB : ℕ → ℝ) (hfS : IsGridPMF fS N)
    (hfB : IsGridPMF fB N) :
    IsGreatest {v : ℝ | ∃ x : ℕ → ℕ → ℝ, IsGridFeasible t fS fB N x ∧ v = gridGFT t fS fB N x}
      (secondBest (Set.Icc 0 1) (gridPrior t fS N) (gridPrior t fB N)) := by sorry

end SecondBestBT
