-- Prove2me | Theorems.Thm_SinkhornHall_Supplement_proposition_3_3
-- name    : SinkhornHall.Supplement.proposition_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T02:08:56.626262+00:00
-- url     : https://prove2.me/theorems/6e5f0b0c-92b5-571e-bc9b-5ff4136a3398
-- title:
--   Proposition 3.3 — $\rho^*$ is the unique minimizer of $D(p\|r)$ over $\mathcal P$
-- statement:
--   Throughout, $A$ is a nonnegative $n\times m$ real matrix with neither zero rows nor zero columns, $r\in\mathbb R^n$ and $c\in\mathbb R^m$ are positive vectors, $R=\sum_i r_i$ and $C=\sum_j c_j$ (it is **not** assumed that $R=C$). A set $X\sqcup Y$ of rows $X$ and columns $Y$ is **stable** if $A_{ij}=0$ for all $i\in X$, $j\in Y$. $\operatorname{Conv}\mathcal S$ is the convex hull in $\mathbb R^2$ of the points $(r(X),c(Y))$ of the stable sets, and $X\sqcup Y$ is **extreme** if $(r(X),c(Y))$ is a nonzero extreme point of $\operatorname{Conv}\mathcal S$. The extreme stable sets ordered as $[n]=X_0\supset X_1\supset\dots\supset X_\theta=\emptyset$, $\emptyset=Y_0\subset\dots\subset Y_\theta=[m]$ give the partitions $I_\kappa=X_{\kappa-1}\setminus X_\kappa$, $J_\kappa=Y_\kappa\setminus Y_{\kappa-1}$ ($\kappa=1,\dots,\theta$), with $R_\kappa=r(I_\kappa)$, $C_\kappa=c(J_\kappa)$, and $\rho^*_i=(C_\kappa/R_\kappa)\,r_i$ for $i\in I_\kappa$. Let $\mathcal P=\{N\mathbf 1: N\in\mathcal C\}$ where $\mathcal C$ is the set of nonnegative matrices supported on the support of $A$ with column sums $c$.
--
--   $\rho^*$ is the unique minimizer of
--
--   $$\inf\ D(p\|r)\quad\text{s.t.}\quad p\in\mathcal P: \tag{3.2}$$
--
--   $\rho^*\in\mathcal P$, $D(\rho^*\|r)\le D(p\|r)$ for every $p\in\mathcal P$, and every $p\in\mathcal P$ with $D(p\|r)\le D(\rho^*\|r)$ equals $\rho^*$.
--
--   Combined with Lemma 2.12 (2) this gives Theorem 3.4.
--
--   Differences from the source:
--   - encoding: $D$ with values in $[-\infty,\infty]$ → `EReal` (`klDiv`, `matKL`), $\top$ when some $r_i=0<p_i$; reason: the paper's $\infty$ convention, same instances
--   - encoding: "the" ordered family of extreme stable sets → every `ExtremeChain` (an enumeration of exactly the extreme stable sets with $X$ strictly decreasing and $Y$ strictly increasing); reason: Lemma 3.1 makes the enumeration unique, so quantifying over every one is the paper's claim
--   - encoding: index sets $[n]$, $[m]$ → arbitrary finite types `ι`, `κ`; reason: every finite type is in bijection with some $[n]$; the empty types ($n=0$ or $m=0$, outside the paper's convention) only add trivially true or vacuous instances
-- source:
--   Hayashi–Hirai–Sakabe, Finding Hall blockers by matrix scaling, arXiv:2204.07425v2, Proposition 3.3, p.13

import Mathlib
import Definitions.Def_SinkhornHall_Model
import Definitions.Def_SinkhornHall_Analysis
import Definitions.Def_SinkhornHall_Supplement_KL
import Definitions.Def_SinkhornHall_Supplement_Extreme

open Finset Filter Topology

namespace SinkhornHall.Supplement

/-- **Proposition 3.3 (ρ* solves (3.2)).**
Hayashi–Hirai–Sakabe, arXiv:2204.07425v2, Proposition 3.3, p.13: "ρ* is the unique minimizer of
(3.2)", where (3.2) (p.11) is "inf. D(p‖r) s.t. p ∈ P" with `P` of (2.9), and (3.7) (p.12)
"ρ*_i := (C_κ/R_κ) r_i for i ∈ I_κ".

Setting of §2 and §3 (pp.4–5, p.8, p.10): `A` is a nonnegative `n × m` matrix with neither zero
rows nor zero columns, `r`, `c` are positive vectors, `R := Σ r_i`, `C := Σ c_j`; `R = C` is not
assumed. `S` is the family of stable sets of `G(A)`.

**Formalization Note.** `D` is `klDiv` in `EReal`. "Unique minimizer" is: `ρ* ∈ P`, `ρ*` attains
the minimum, and every `p ∈ P` attaining it equals `ρ*`. `ρ*` is `ExtremeChain.rhoStar` of the
ordered family of extreme stable sets; the statement holds for every such enumeration. -/
theorem proposition_3_3 {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : Matrix ι κ ℝ) (r : ι → ℝ) (c : κ → ℝ) (hA : ∀ i j, 0 ≤ A i j)
    (hrow : ∀ i, ∃ j, 0 < A i j) (hcol : ∀ j, ∃ i, 0 < A i j) (hr : ∀ i, 0 < r i)
    (hc : ∀ j, 0 < c j)
    (ch : ExtremeChain A r c) :
    ch.rhoStar ∈ marginalPolytope A c ∧
      (∀ p ∈ marginalPolytope A c, SinkhornHall.klDiv ch.rhoStar r ≤ SinkhornHall.klDiv p r) ∧
      (∀ p ∈ marginalPolytope A c,
        SinkhornHall.klDiv p r ≤ SinkhornHall.klDiv ch.rhoStar r → p = ch.rhoStar) := by sorry

end SinkhornHall.Supplement
