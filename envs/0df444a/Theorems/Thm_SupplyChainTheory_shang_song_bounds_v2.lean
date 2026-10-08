-- Prove2me | Theorems.Thm_SupplyChainTheory_shang_song_bounds_v2
-- name    : SupplyChainTheory.shang_song_bounds_v2
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-10-06T06:42:54.337632+00:00
-- url     : https://prove2.me/theorems/2796603e-1845-4643-a55b-032e7b03d3ca
-- title:
--   Theorem 6.4 (Shang and Song): $g^l_j\le g_j\le g^u_j$ and $S^l_j\le S^*_j\le S^u_j$, for nonnegative demands
-- statement:
--   **Theorem 6.4 (Shang and Song 2003).** In the serial system of §6.2 with echelon holding costs $h_j>0$, stockout cost $p>0$ and nonnegative lead-time demands $D_j$ of finite mean, let $S^*$ be built by the sequential minimization of Theorem 6.3 and let $g^l_j$ and $g^u_j$ be the truncated cost (6.31) with every local holding cost replaced by $h_j$ (lower) or by $\sum_{k=1}^jh_k$ (upper): the single-stage newsvendor cost with demand $\tilde D_j=D_1+\dots+D_j$ and stockout cost $p+h'_{j+1}$, plus the holding cost of the pipeline stock $\mathbb E[D_1]+\dots+\mathbb E[D_{j-1}]$ at the replaced rate. Then for any $j$ and $y$:
--
--   (a) $g^l_j(y)\le g_j(y)\le g^u_j(y)$;
--
--   (b) $S^l_j\le S^*_j\le S^u_j$, where, as the book says on p. 200, $S^u_j$ minimizes $g^l_j$ and $S^l_j$ minimizes $g^u_j$: the cheaper holding rate $h_j$ of the lower bound has the larger fractile, so it is the upper base-stock bound.
--
--   The bounds come from the truncated system of (6.31): with all local holding costs equal, all inventory is held at stage 1 and the $j$-stage system collapses to a single stage with lead time $L_1+\dots+L_j$. Their average (6.32) is the Shang–Song heuristic, accurate to a fraction of a percent on the authors' test instances.
--
--   **Formalization Note.** The retired version let the lead-time demand laws take negative values; the inventory models of the book assume nonnegative demands (the newsvendor and echelon-cost derivations and the pipeline-stock interpretation presuppose $D\ge0$), and with a negative demand the pipeline-stock term of $g^u_j$ turns negative while the echelon accounting of $g_j$ does not, so (a) fails (accepted disproof with $D_1=\delta_{-1}$). The new statement adds the standing convention $D_j([0,\infty)^c)=0$ for every $j$ and is otherwise unchanged. The bounding functions keep the pipeline holding cost that (6.31) charges on stock in transit; the book drops it when it writes the minimizers, since it does not affect them, but part (a) compares values and fails without it (in Example 6.1, $g_2(S^*_2)=20.82$ while the single-stage cost alone is $12.2$). Part (b) asserts the existence of a minimizer $S^l_j$ of $g^u_j$ and a minimizer $S^u_j$ of $g^l_j$ bracketing $S^*_j$; when the fractiles of $\tilde D_j$ are unique these are the book's $\tilde F_j^{-1}$ values. In Example 6.2 at $j=2$: $S^l_2=11.71\le S^*_2=12.02\le S^u_2=12.35$. Pairing the minimizers the other way would assert $12.35\le12.02$.
-- source:
--   Lawrence V. Snyder and Zuo-Jun Max Shen, Fundamentals of Supply Chain Theory, 2nd ed., Wiley 2019, DOI 10.1002/9781119584445, p. 201, Sect. 6.2.3, Theorem 6.4; the bounding functions are defined on p. 200; demands are nonnegative random variables throughout the inventory chapters; after Shang and Song (2003)

import Definitions.Def_SupplyChainTheory_multiechelon

namespace SupplyChainTheory

/-- Snyder & Shen, *Fundamentals of Supply Chain Theory*, 2nd ed., p. 201, Theorem 6.4
(Shang & Song 2003): in the serial system of §6.2 with echelon holding costs `h_j > 0`, stockout
cost `p > 0` and **nonnegative** lead-time demands `D_j` of finite mean, with `S*` the
sequentially optimal vector of Theorem 6.3 and `gˡ_j`, `gᵘ_j` the newsvendor-type bounding
functions of p. 200: (a) `gˡ_j(y) ≤ g_j(y | S*) ≤ gᵘ_j(y)` for every `y`, and (b) a minimizer
`Sˡ_j` of `gᵘ_j` and a minimizer `Sᵘ_j` of `gˡ_j` bracket `S*_j`.

Corrected version: the demands are nonnegative random variables (`D_j([0, ∞)^c) = 0`), the
standing convention of the inventory models of the book; the retired statement allowed demand
laws with negative values, under which the pipeline-stock term of `gᵘ_j` turns negative and (a)
fails. -/
theorem shang_song_bounds_v2 (N : ℕ) (h : ℕ → ℝ) (p : ℝ) (D : ℕ → MeasureTheory.Measure ℝ)
    [∀ j, MeasureTheory.IsProbabilityMeasure (D j)]
    (hD : ∀ j, MeasureTheory.Integrable (fun x => x) (D j))
    (hD0 : ∀ j, D j (Set.Iio 0) = 0)
    (hh : ∀ j, 0 < h j) (hp : 0 < p) (Sstar : ℕ → ℝ) (hS : CSSequential N h p D Sstar)
    (j : ℕ) (hj1 : 1 ≤ j) (hjN : j ≤ N) :
    (∀ y, ssLower N h p D j y ≤ csG N h p D Sstar j y
        ∧ csG N h p D Sstar j y ≤ ssUpper N h p D j y)
      ∧ ∃ Sl Su : ℝ, IsMinOn (ssUpper N h p D j) Set.univ Sl
          ∧ IsMinOn (ssLower N h p D j) Set.univ Su ∧ Sl ≤ Sstar j ∧ Sstar j ≤ Su := by sorry

end SupplyChainTheory
