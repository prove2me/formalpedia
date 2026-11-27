-- Prove2me | Theorems.Thm_SinkhornHall_Supplement_theorem_3_6
-- name    : SinkhornHall.Supplement.theorem_3_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T02:10:38.165186+00:00
-- url     : https://prove2.me/theorems/16084d3e-96ab-4356-a61e-89d503177c59
-- title:
--   Theorem 3.6 (companion theorem) — the Sinkhorn limit is $M^*=\bigoplus R_\kappa B_{\kappa,\alpha}$, $N^*=\bigoplus C_\kappa B_{\kappa,\alpha}$
-- statement:
--   Throughout, $A$ is a nonnegative $n\times m$ real matrix with neither zero rows nor zero columns, $r\in\mathbb R^n$ and $c\in\mathbb R^m$ are positive vectors, $R=\sum_i r_i$ and $C=\sum_j c_j$ (it is **not** assumed that $R=C$). For a matrix $N$, $R(N)_{ij}=(r_i/(N\mathbf 1)_i)N_{ij}$ and $C(N)_{ij}=(c_j/(N^\top\mathbf 1)_j)N_{ij}$ are its row and column normalizations, and the **Sinkhorn sequence** is
--
--   $$N_0=C(A),\qquad M_k=R(N_k),\qquad N_{k+1}=C(M_k)\quad(k=0,1,2,\dots).$$
--
--   $D(N\|M)=\sum_{i,j}N_{ij}\log(N_{ij}/M_{ij})$ is the KL divergence with $0\log(0/x)=0$ and $x\log(x/0)=+\infty$ for $x>0$; the sums of $N$ and $M$ may differ, so $D$ can be negative. The spaces are $\mathcal M=\{M: M_{ij}=0 \text{ if } A_{ij}=0,\ M_{ij}\ge0 \text{ if } A_{ij}>0\}$, $\mathcal R=\{M\in\mathcal M: M\mathbf 1=r\}$ and $\mathcal C=\{M\in\mathcal M: M^\top\mathbf 1=c\}$. A set $X\sqcup Y$ of rows $X$ and columns $Y$ is **stable** if $A_{ij}=0$ for all $i\in X$, $j\in Y$. $\operatorname{Conv}\mathcal S$ is the convex hull in $\mathbb R^2$ of the points $(r(X),c(Y))$ of the stable sets, and $X\sqcup Y$ is **extreme** if $(r(X),c(Y))$ is a nonzero extreme point of $\operatorname{Conv}\mathcal S$. The extreme stable sets ordered as $[n]=X_0\supset X_1\supset\dots\supset X_\theta=\emptyset$, $\emptyset=Y_0\subset\dots\subset Y_\theta=[m]$ give the partitions $I_\kappa=X_{\kappa-1}\setminus X_\kappa$, $J_\kappa=Y_\kappa\setminus Y_{\kappa-1}$ ($\kappa=1,\dots,\theta$), with $R_\kappa=r(I_\kappa)$, $C_\kappa=c(J_\kappa)$, and $\rho^*_i=(C_\kappa/R_\kappa)\,r_i$ for $i\in I_\kappa$. The refined blocks $I_{\kappa,\alpha}\times J_{\kappa,\alpha}$ come from a maximal chain in the family $\mathcal S_\kappa$ of maximizers of (3.9) at the $\kappa$-th critical parameter (3.10).
--
--   The Sinkhorn limit $(M^*,N^*)$ is
--
--   $$M^*=\bigoplus_{\kappa\in[\theta],\,\alpha\in[\alpha_\kappa]}R_\kappa B_{\kappa,\alpha},\qquad N^*=\bigoplus_{\kappa\in[\theta],\,\alpha\in[\alpha_\kappa]}C_\kappa B_{\kappa,\alpha}, \tag{3.11}$$
--
--   where $B_{\kappa,\alpha}$ is the (unique) $(r^{\kappa,\alpha}/R_\kappa,\ c^{\kappa,\alpha}/C_\kappa)$-scaling of $A[I_{\kappa,\alpha},J_{\kappa,\alpha}]$ and all entries outside the diagonal blocks are $0$. Precisely: the chains exist; for every choice of them every block has such a scaling; and for every choice of scalings $B_{\kappa,\alpha}$, $M_k\to\bigoplus R_\kappa B_{\kappa,\alpha}$ and $N_k\to\bigoplus C_\kappa B_{\kappa,\alpha}$.
--
--   This is the complete description of the limit of the Sinkhorn algorithm on a nonscalable matrix, a refinement of the block-triangular form of Aas and, for $(r,c)=(\mathbf 1,\mathbf 1)$, of the Dulmage–Mendelsohn decomposition.
--
--   Differences from the source:
--   - encoding: "the" ordered family of extreme stable sets → every `ExtremeChain` (an enumeration of exactly the extreme stable sets with $X$ strictly decreasing and $Y$ strictly increasing); reason: Lemma 3.1 makes the enumeration unique, so quantifying over every one is the paper's claim (existence asserted as a separate conjunct)
--   - reading: critical parameter, "a minimizer is not unique" (p.13) → the maximizer of (3.9) is not unique; reason: (3.9) is a maximization, the minimizer refers to the equivalent minimum-cut problem
--   - encoding: "choose a maximal chain" in each $\mathcal S_\kappa$ → every `RefinedChain` (increasing enumeration of all critical parameters, a chain in each $\mathcal S_\kappa$ from $X_{\kappa-1}\sqcup Y_{\kappa-1}$ to $X_\kappa\sqcup Y_\kappa$ to which no member of $\mathcal S_\kappa$ can be added); reason: the paper allows any choice (existence asserted)
--   - encoding: "the (unique) scaling $B_{\kappa,\alpha}$" → existence of a scaling for every block, and the convergence for every family of scalings; reason: covers uniqueness of the limit without assuming Theorem 2.1 (3)
--   - encoding: "the Sinkhorn limit is given by" → $M_k$ and $N_k$ converge to the two block-diagonal matrices; reason: identifies the limit and asserts its existence, as Theorem 2.10 does
--   - encoding: index sets $[n]$, $[m]$ ($n$ positive) → finite types `ι`, `κ` with `ι` nonempty (then `κ` is nonempty because no row is zero); reason: the paper's convention (p.4)
-- source:
--   Hayashi–Hirai–Sakabe, Finding Hall blockers by matrix scaling, arXiv:2204.07425v2, Theorem 3.6, (3.11), p.14

import Mathlib
import Definitions.Def_SinkhornHall_Model
import Definitions.Def_SinkhornHall_Analysis
import Definitions.Def_SinkhornHall_Supplement_KL
import Definitions.Def_SinkhornHall_Supplement_Extreme

open Finset Filter Topology

namespace SinkhornHall.Supplement

/-- **Theorem 3.6 (the Sinkhorn limit).**
Hayashi–Hirai–Sakabe, arXiv:2204.07425v2, Theorem 3.6, (3.11), p.14: "The Sinkhorn limit (M*, N*)
is given by M* = ⊕_{κ∈[θ], α∈[α_κ]} R_κ B_{κ,α}, N* = ⊕_{κ∈[θ], α∈[α_κ]} C_κ B_{κ,α}, where
B_{κ,α} denotes the (unique) (r^{κ,α}/R_κ, c^{κ,α}/C_κ)-scaling of A[I_{κ,α}, J_{κ,α}]."

Setting of §2 and §3 (pp.4–5, p.8, p.10): `A` is a nonnegative `n × m` matrix with neither zero
rows nor zero columns, `r`, `c` are positive vectors, `R := Σ r_i`, `C := Σ c_j`; `R = C` is not
assumed. `S` is the family of stable sets of `G(A)`.
The blocks `I_{κ,α} × J_{κ,α}` come from a maximal chain in each `S_κ` (pp.13–14, (3.10)).

**Formalization Note.** The conclusion has three parts: the objects of pp.12–14 exist (an
`ExtremeChain` with a `RefinedChain`); for every such choice every block has an
`(r^{κ,α}/R_κ, c^{κ,α}/C_κ)`-scaling; and for every family `B` of such scalings, `M_k` converges to
`⊕ R_κ B_{κ,α}` and `N_k` to `⊕ C_κ B_{κ,α}` (entries outside the diagonal blocks are `0`). This
covers "(unique)": the limit does not depend on the chosen scalings. The row set is nonempty (the
paper's `[n]`, p.4). -/
theorem theorem_3_6 {ι κ : Type*} [Fintype ι] [Fintype κ] [Nonempty ι]
    (A : Matrix ι κ ℝ) (r : ι → ℝ) (c : κ → ℝ) (hA : ∀ i j, 0 ≤ A i j)
    (hrow : ∀ i, ∃ j, 0 < A i j) (hcol : ∀ j, ∃ i, 0 < A i j) (hr : ∀ i, 0 < r i)
    (hc : ∀ j, 0 < c j) :
    (∃ ch : ExtremeChain A r c, Nonempty (RefinedChain ch)) ∧
      ∀ (ch : ExtremeChain A r c) (rc : RefinedChain ch),
        (∀ (k : Fin ch.θ) (a : Fin (rc.α k)),
          Scalable (fun (i : {i // i ∈ rc.I k a}) (j : {j // j ∈ rc.J k a}) => A i j)
            (fun i => r i / ch.Rk k) (fun j => c j / ch.Ck k)) ∧
        ∀ B : (k : Fin ch.θ) → (a : Fin (rc.α k)) →
            Matrix {i // i ∈ rc.I k a} {j // j ∈ rc.J k a} ℝ,
          (∀ (k : Fin ch.θ) (a : Fin (rc.α k)),
            IsScaling (fun (i : {i // i ∈ rc.I k a}) (j : {j // j ∈ rc.J k a}) => A i j)
              (fun i => r i / ch.Rk k) (fun j => c j / ch.Ck k) (B k a)) →
          Tendsto (sinkhornM A r c) atTop (𝓝 (blockDiag rc ch.Rk B)) ∧
            Tendsto (sinkhornN A r c) atTop (𝓝 (blockDiag rc ch.Ck B)) := by sorry

end SinkhornHall.Supplement
