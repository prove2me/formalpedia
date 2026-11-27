-- Prove2me | Theorems.Thm_SinkhornHall_Supplement_lemma_3_2
-- name    : SinkhornHall.Supplement.lemma_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T02:08:30.24537+00:00
-- url     : https://prove2.me/theorems/cb841031-189b-5636-b284-3d2d20b7f2a5
-- title:
--   Lemma 3.2 — diagonal blocks $A[I_\kappa,J_\kappa]$ are approximately scalable and $R_\kappa/C_\kappa$ increases
-- statement:
--   Throughout, $A$ is a nonnegative $n\times m$ real matrix with neither zero rows nor zero columns, $r\in\mathbb R^n$ and $c\in\mathbb R^m$ are positive vectors, $R=\sum_i r_i$ and $C=\sum_j c_j$ (it is **not** assumed that $R=C$). A set $X\sqcup Y$ of rows $X$ and columns $Y$ is **stable** if $A_{ij}=0$ for all $i\in X$, $j\in Y$. $\operatorname{Conv}\mathcal S$ is the convex hull in $\mathbb R^2$ of the points $(r(X),c(Y))$ of the stable sets, and $X\sqcup Y$ is **extreme** if $(r(X),c(Y))$ is a nonzero extreme point of $\operatorname{Conv}\mathcal S$. The extreme stable sets ordered as $[n]=X_0\supset X_1\supset\dots\supset X_\theta=\emptyset$, $\emptyset=Y_0\subset\dots\subset Y_\theta=[m]$ give the partitions $I_\kappa=X_{\kappa-1}\setminus X_\kappa$, $J_\kappa=Y_\kappa\setminus Y_{\kappa-1}$ ($\kappa=1,\dots,\theta$), with $R_\kappa=r(I_\kappa)$, $C_\kappa=c(J_\kappa)$, and $\rho^*_i=(C_\kappa/R_\kappa)\,r_i$ for $i\in I_\kappa$.
--
--   1. Each submatrix $A[I_\kappa,J_\kappa]$ is approximately $(r_\kappa/R_\kappa,\ c_\kappa/C_\kappa)$-scalable, where $r_\kappa$, $c_\kappa$ are the restrictions of $r$, $c$ to $I_\kappa$, $J_\kappa$.
--   2. $$\frac{R_1}{C_1}<\frac{R_2}{C_2}<\dots<\frac{R_\theta}{C_\theta}.$$
--
--   Both parts are used to show that $\rho^*$ solves (3.2) (Proposition 3.3).
--
--   Differences from the source:
--   - encoding: "the" ordered family of extreme stable sets → every `ExtremeChain` (an enumeration of exactly the extreme stable sets with $X$ strictly decreasing and $Y$ strictly increasing); reason: Lemma 3.1 makes the enumeration unique, so quantifying over every one is the paper's claim
--   - encoding: approximate scalability → the base `ApproxScalable` (positive scalings with $\ell_1$ marginal error below every $\varepsilon>0$); reason: the paper allows any norm, all are equivalent
--   - encoding: index sets $[n]$, $[m]$ → arbitrary finite types `ι`, `κ`; reason: every finite type is in bijection with some $[n]$; the empty types ($n=0$ or $m=0$, outside the paper's convention) only add trivially true or vacuous instances
-- source:
--   Hayashi–Hirai–Sakabe, Finding Hall blockers by matrix scaling, arXiv:2204.07425v2, Lemma 3.2, p.12

import Mathlib
import Definitions.Def_SinkhornHall_Model
import Definitions.Def_SinkhornHall_Analysis
import Definitions.Def_SinkhornHall_Supplement_KL
import Definitions.Def_SinkhornHall_Supplement_Extreme

open Finset Filter Topology

namespace SinkhornHall.Supplement

/-- **Lemma 3.2.**
Hayashi–Hirai–Sakabe, arXiv:2204.07425v2, Lemma 3.2, p.12: "(1) Each submatrix A[I_κ, J_κ] is
approximately (r_κ/R_κ, c_κ/C_κ)-scalable. (2) It holds R_1/C_1 < R_2/C_2 < ⋯ < R_θ/C_θ."

Setting of §2 and §3 (pp.4–5, p.8, p.10): `A` is a nonnegative `n × m` matrix with neither zero
rows nor zero columns, `r`, `c` are positive vectors, `R := Σ r_i`, `C := Σ c_j`; `R = C` is not
assumed. `S` is the family of stable sets of `G(A)`.
`X_0 ⊔ Y_0, …, X_θ ⊔ Y_θ` are the extreme stable sets ordered as on p.12
(`[n] = X_0 ⊃ ⋯ ⊃ X_θ = ∅`, `∅ = Y_0 ⊂ ⋯ ⊂ Y_θ = [m]`), `I_κ = X_{κ−1} \ X_κ`,
`J_κ = Y_κ \ Y_{κ−1}` (3.6), `r_κ`, `c_κ` the restrictions of `r`, `c`, `R_κ = r(I_κ)`,
`C_κ = c(J_κ)`.

**Formalization Note.** The ordered family is an `ExtremeChain`; the statement holds for every
such enumeration (Lemma 3.1 makes it unique). `k : Fin θ` stands for `κ = k + 1`. The submatrix
`A[I_κ, J_κ]` is indexed by the subtypes of `I_κ` and `J_κ`; approximate scalability is the base
`ApproxScalable` (`ℓ₁` marginal error below every `ε > 0` for some positive scaling). -/
theorem lemma_3_2 {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : Matrix ι κ ℝ) (r : ι → ℝ) (c : κ → ℝ) (hA : ∀ i j, 0 ≤ A i j)
    (hrow : ∀ i, ∃ j, 0 < A i j) (hcol : ∀ j, ∃ i, 0 < A i j) (hr : ∀ i, 0 < r i)
    (hc : ∀ j, 0 < c j)
    (ch : ExtremeChain A r c) :
    (∀ k : Fin ch.θ, SinkhornHall.ApproxScalable
        (fun (i : {i // i ∈ ch.I k}) (j : {j // j ∈ ch.J k}) => A i j)
        (fun i => r i / ch.Rk k) (fun j => c j / ch.Ck k)) ∧
    StrictMono (fun k : Fin ch.θ => ch.Rk k / ch.Ck k) := by sorry

end SinkhornHall.Supplement
