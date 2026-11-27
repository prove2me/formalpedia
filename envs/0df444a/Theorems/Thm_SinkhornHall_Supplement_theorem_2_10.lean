-- Prove2me | Theorems.Thm_SinkhornHall_Supplement_theorem_2_10
-- name    : SinkhornHall.Supplement.theorem_2_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T02:06:43.216474+00:00
-- url     : https://prove2.me/theorems/13b03fb7-9be1-5c35-bdf5-1d3179660b8a
-- title:
--   Theorem 2.10 (companion theorem) — the Sinkhorn sequence $(M_k,N_k)$ converges to a minimizer of (2.7)
-- statement:
--   Throughout, $A$ is a nonnegative $n\times m$ real matrix with neither zero rows nor zero columns, $r\in\mathbb R^n$ and $c\in\mathbb R^m$ are positive vectors, $R=\sum_i r_i$ and $C=\sum_j c_j$ (it is **not** assumed that $R=C$). For a matrix $N$, $R(N)_{ij}=(r_i/(N\mathbf 1)_i)N_{ij}$ and $C(N)_{ij}=(c_j/(N^\top\mathbf 1)_j)N_{ij}$ are its row and column normalizations, and the **Sinkhorn sequence** is
--
--   $$N_0=C(A),\qquad M_k=R(N_k),\qquad N_{k+1}=C(M_k)\quad(k=0,1,2,\dots).$$
--
--   $D(N\|M)=\sum_{i,j}N_{ij}\log(N_{ij}/M_{ij})$ is the KL divergence with $0\log(0/x)=0$ and $x\log(x/0)=+\infty$ for $x>0$; the sums of $N$ and $M$ may differ, so $D$ can be negative. The spaces are $\mathcal M=\{M: M_{ij}=0 \text{ if } A_{ij}=0,\ M_{ij}\ge0 \text{ if } A_{ij}>0\}$, $\mathcal R=\{M\in\mathcal M: M\mathbf 1=r\}$ and $\mathcal C=\{M\in\mathcal M: M^\top\mathbf 1=c\}$.
--
--   The sequence $(M_k,N_k)$ converges, and its limit $(M^*,N^*)$ is a minimizer of
--
--   $$\inf\ D(N\|M)\quad\text{s.t.}\quad M\in\mathcal R,\ N\in\mathcal C. \tag{2.7}$$
--
--   The limit is the **Sinkhorn limit** of $A$. In the approximately scalable case it is the $(r,c)$-scaling limit; in the nonscalable case it is the pair closest in KL divergence between the row-feasible and column-feasible matrices, whose structure §3 describes.
--
--   Differences from the source:
--   - encoding: convergence of matrices → entrywise convergence (`Tendsto` in the product topology); reason: all norms on a finite-dimensional space agree
--   - encoding: index sets $[n]$, $[m]$ → arbitrary finite types `ι`, `κ`; reason: every finite type is in bijection with some $[n]$; the empty types ($n=0$ or $m=0$, outside the paper's convention) only add trivially true or vacuous instances
-- source:
--   Hayashi–Hirai–Sakabe, Finding Hall blockers by matrix scaling, arXiv:2204.07425v2, Theorem 2.10, p.9 (proof pp.8–9)

import Mathlib
import Definitions.Def_SinkhornHall_Model
import Definitions.Def_SinkhornHall_Analysis
import Definitions.Def_SinkhornHall_Supplement_KL

open Finset Filter Topology

namespace SinkhornHall.Supplement

/-- **Theorem 2.10 (convergence of the Sinkhorn sequence).**
Hayashi–Hirai–Sakabe, arXiv:2204.07425v2, Theorem 2.10, p.9 (proof pp.8–9): "The sequence
(M_k, N_k) converges to a minimizer (M*, N*) of (2.7)."

Setting of §2 (pp.4–5, p.8): `A` is a nonnegative `n × m` matrix with neither zero rows nor
zero columns, `r`, `c` are positive vectors, `R := Σ r_i`, `C := Σ c_j`; `R = C` is not assumed.
`(M_k, N_k)` is the Sinkhorn sequence (2.6); (2.7) is the minimization of `D(N‖M)` over
`M ∈ R`, `N ∈ C`.

**Formalization Note.** Convergence is entrywise (the product topology on `Matrix ι κ ℝ`); the
limit pair is asserted to exist and to satisfy `IsMinimizer27`. -/
theorem theorem_2_10 {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : Matrix ι κ ℝ) (r : ι → ℝ) (c : κ → ℝ) (hA : ∀ i j, 0 ≤ A i j)
    (hrow : ∀ i, ∃ j, 0 < A i j) (hcol : ∀ j, ∃ i, 0 < A i j) (hr : ∀ i, 0 < r i)
    (hc : ∀ j, 0 < c j) :
    ∃ Mstar Nstar : Matrix ι κ ℝ, Tendsto (sinkhornM A r c) atTop (𝓝 Mstar) ∧
      Tendsto (sinkhornN A r c) atTop (𝓝 Nstar) ∧ IsMinimizer27 A r c Mstar Nstar := by sorry

end SinkhornHall.Supplement
