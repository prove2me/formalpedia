-- Prove2me | Theorems.Thm_SinkhornHall_Supplement_theorem_3_4
-- name    : SinkhornHall.Supplement.theorem_3_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T02:09:19.638791+00:00
-- url     : https://prove2.me/theorems/6dac635a-f78f-5635-8406-1ec882887944
-- title:
--   Theorem 3.4 (companion theorem) — the row marginal of the Sinkhorn limit is $\rho^*$
-- statement:
--   Throughout, $A$ is a nonnegative $n\times m$ real matrix with neither zero rows nor zero columns, $r\in\mathbb R^n$ and $c\in\mathbb R^m$ are positive vectors, $R=\sum_i r_i$ and $C=\sum_j c_j$ (it is **not** assumed that $R=C$). For a matrix $N$, $R(N)_{ij}=(r_i/(N\mathbf 1)_i)N_{ij}$ and $C(N)_{ij}=(c_j/(N^\top\mathbf 1)_j)N_{ij}$ are its row and column normalizations, and the **Sinkhorn sequence** is
--
--   $$N_0=C(A),\qquad M_k=R(N_k),\qquad N_{k+1}=C(M_k)\quad(k=0,1,2,\dots).$$
--
--   $D(N\|M)=\sum_{i,j}N_{ij}\log(N_{ij}/M_{ij})$ is the KL divergence with $0\log(0/x)=0$ and $x\log(x/0)=+\infty$ for $x>0$; the sums of $N$ and $M$ may differ, so $D$ can be negative. The spaces are $\mathcal M=\{M: M_{ij}=0 \text{ if } A_{ij}=0,\ M_{ij}\ge0 \text{ if } A_{ij}>0\}$, $\mathcal R=\{M\in\mathcal M: M\mathbf 1=r\}$ and $\mathcal C=\{M\in\mathcal M: M^\top\mathbf 1=c\}$. A set $X\sqcup Y$ of rows $X$ and columns $Y$ is **stable** if $A_{ij}=0$ for all $i\in X$, $j\in Y$. $\operatorname{Conv}\mathcal S$ is the convex hull in $\mathbb R^2$ of the points $(r(X),c(Y))$ of the stable sets, and $X\sqcup Y$ is **extreme** if $(r(X),c(Y))$ is a nonzero extreme point of $\operatorname{Conv}\mathcal S$. The extreme stable sets ordered as $[n]=X_0\supset X_1\supset\dots\supset X_\theta=\emptyset$, $\emptyset=Y_0\subset\dots\subset Y_\theta=[m]$ give the partitions $I_\kappa=X_{\kappa-1}\setminus X_\kappa$, $J_\kappa=Y_\kappa\setminus Y_{\kappa-1}$ ($\kappa=1,\dots,\theta$), with $R_\kappa=r(I_\kappa)$, $C_\kappa=c(J_\kappa)$, and $\rho^*_i=(C_\kappa/R_\kappa)\,r_i$ for $i\in I_\kappa$.
--
--   The extreme stable sets can be ordered as above, and for the Sinkhorn limit $N^*$,
--
--   $$p^*=N^*\mathbf 1=\rho^*,\qquad\text{i.e. } (N^*\mathbf 1)_i=\frac{C_\kappa}{R_\kappa}\,r_i\quad(i\in I_\kappa).$$
--
--   This is an explicit formula for the limit of the row marginals in the nonscalable case; in the doubly stochastic setting it says that sorting the marginals of $N^*$ recovers every extreme set $X_\kappa$, the basis of Theorem 4.3.
--
--   Differences from the source:
--   - encoding: "the" ordered family of extreme stable sets → every `ExtremeChain` (an enumeration of exactly the extreme stable sets with $X$ strictly decreasing and $Y$ strictly increasing); reason: Lemma 3.1 makes the enumeration unique, so quantifying over every one is the paper's claim (existence of the enumeration is asserted as a separate conjunct)
--   - encoding: the Sinkhorn limit $(M^*,N^*)$ (the limit of $(M_k,N_k)$, Theorem 2.10) → a hypothesis that $(M_k,N_k)$ (or $N_k$) converges to the given matrices; reason: the paper defines the limit through Theorem 2.10, which the mission states separately; for the actual limit the statements coincide
--   - encoding: index sets $[n]$, $[m]$ ($n$ positive) → finite types `ι`, `κ` with `ι` nonempty (then `κ` is nonempty because no row is zero); reason: the paper's $[n]$ (p.4); with no rows there are no extreme stable sets
-- source:
--   Hayashi–Hirai–Sakabe, Finding Hall blockers by matrix scaling, arXiv:2204.07425v2, Theorem 3.4, p.13

import Mathlib
import Definitions.Def_SinkhornHall_Model
import Definitions.Def_SinkhornHall_Analysis
import Definitions.Def_SinkhornHall_Supplement_KL
import Definitions.Def_SinkhornHall_Supplement_Extreme

open Finset Filter Topology

namespace SinkhornHall.Supplement

/-- **Theorem 3.4 (the marginal of the Sinkhorn limit).**
Hayashi–Hirai–Sakabe, arXiv:2204.07425v2, Theorem 3.4, p.13: "ρ* = p* (= N*1)", where `N*` is the
Sinkhorn limit (Theorem 2.10), `p* := N*1` (p.9) and `ρ*_i := (C_κ/R_κ) r_i` for `i ∈ I_κ` (3.7),
built from the extreme stable sets ordered as on p.12.

Setting of §2 and §3 (pp.4–5, p.8, p.10): `A` is a nonnegative `n × m` matrix with neither zero
rows nor zero columns, `r`, `c` are positive vectors, `R := Σ r_i`, `C := Σ c_j`; `R = C` is not
assumed. `S` is the family of stable sets of `G(A)`.

**Formalization Note.** The conclusion has two parts: the extreme stable sets admit the ordering of
p.12 (an `ExtremeChain` exists), and for every such ordering and every limit `N*` of `N_k`, the
row sums of `N*` are `ρ*`. The row set is nonempty (the paper's `[n]` for a positive integer
`n`, p.4). -/
theorem theorem_3_4 {ι κ : Type*} [Fintype ι] [Fintype κ] [Nonempty ι]
    (A : Matrix ι κ ℝ) (r : ι → ℝ) (c : κ → ℝ) (hA : ∀ i j, 0 ≤ A i j)
    (hrow : ∀ i, ∃ j, 0 < A i j) (hcol : ∀ j, ∃ i, 0 < A i j) (hr : ∀ i, 0 < r i)
    (hc : ∀ j, 0 < c j) :
    Nonempty (ExtremeChain A r c) ∧
      ∀ (ch : ExtremeChain A r c) (Nstar : Matrix ι κ ℝ),
        Tendsto (sinkhornN A r c) atTop (𝓝 Nstar) →
          (fun i => ∑ j, Nstar i j) = ch.rhoStar := by sorry

end SinkhornHall.Supplement
