-- Prove2me | Theorems.Thm_SinkhornHall_Supplement_lemma_3_1
-- name    : SinkhornHall.Supplement.lemma_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T02:08:03.90206+00:00
-- url     : https://prove2.me/theorems/8b23e4cc-df28-4747-b606-53d68862189d
-- title:
--   Lemma 3.1 — extreme stable sets are nested, and $(3.4)$ is injective on them
-- statement:
--   Throughout, $A$ is a nonnegative $n\times m$ real matrix with neither zero rows nor zero columns, $r\in\mathbb R^n$ and $c\in\mathbb R^m$ are positive vectors, $R=\sum_i r_i$ and $C=\sum_j c_j$ (it is **not** assumed that $R=C$). A set $X\sqcup Y$ of rows $X$ and columns $Y$ is **stable** if $A_{ij}=0$ for all $i\in X$, $j\in Y$. $\operatorname{Conv}\mathcal S$ is the convex hull in $\mathbb R^2$ of the points $(r(X),c(Y))$ of the stable sets, and $X\sqcup Y$ is **extreme** if $(r(X),c(Y))$ is a nonzero extreme point of $\operatorname{Conv}\mathcal S$.
--
--   For extreme stable sets $X\sqcup Y$ and $X'\sqcup Y'$:
--
--   1. if $r(X)\ge r(X')$ and $c(Y)\le c(Y')$, then $X\supseteq X'$ and $Y\subseteq Y'$;
--   2. in particular, if $(r(X),c(Y))=(r(X'),c(Y'))$ then $X=X'$ and $Y=Y'$ (the map $X\sqcup Y\mapsto(r(X),c(Y))$ of (3.4) is injective on extreme stable sets).
--
--   This is what orders the extreme stable sets into the chain $X_0\supset\dots\supset X_\theta$ used throughout §3.
--
--   Differences from the source:
--   - encoding: index sets $[n]$, $[m]$ → arbitrary finite types `ι`, `κ`; reason: every finite type is in bijection with some $[n]$; the empty types ($n=0$ or $m=0$, outside the paper's convention) only add trivially true or vacuous instances
-- source:
--   Hayashi–Hirai–Sakabe, Finding Hall blockers by matrix scaling, arXiv:2204.07425v2, Lemma 3.1, p.11 (proof pp.11–12)

import Mathlib
import Definitions.Def_SinkhornHall_Model
import Definitions.Def_SinkhornHall_Analysis
import Definitions.Def_SinkhornHall_Supplement_KL
import Definitions.Def_SinkhornHall_Supplement_Extreme

open Finset Filter Topology

namespace SinkhornHall.Supplement

/-- **Lemma 3.1 (extreme stable sets are nested).**
Hayashi–Hirai–Sakabe, arXiv:2204.07425v2, Lemma 3.1, p.11: "For extreme stable sets X ⊔ Y,
X′ ⊔ Y′, if r(X) ≥ r(X′) and c(Y) ≤ c(Y′), then X ⊇ X′ and Y ⊆ Y′. In particular, the map (3.4) is
injective on the family of extreme stable sets."

Setting of §2 and §3 (pp.4–5, p.8, p.10): `A` is a nonnegative `n × m` matrix with neither zero
rows nor zero columns, `r`, `c` are positive vectors, `R := Σ r_i`, `C := Σ c_j`; `R = C` is not
assumed. `S` is the family of stable sets of `G(A)`.
The map (3.4) is `X ⊔ Y ↦ (r(X), c(Y))`; extreme stable sets are those mapped to a nonzero extreme
point of `Conv S` (p.11). -/
theorem lemma_3_1 {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : Matrix ι κ ℝ) (r : ι → ℝ) (c : κ → ℝ) (hA : ∀ i j, 0 ≤ A i j)
    (hrow : ∀ i, ∃ j, 0 < A i j) (hcol : ∀ j, ∃ i, 0 < A i j) (hr : ∀ i, 0 < r i)
    (hc : ∀ j, 0 < c j) :
    (∀ (X X' : Finset ι) (Y Y' : Finset κ), IsExtremeStable A r c X Y →
      IsExtremeStable A r c X' Y' → ∑ i ∈ X', r i ≤ ∑ i ∈ X, r i →
      ∑ j ∈ Y, c j ≤ ∑ j ∈ Y', c j → X' ⊆ X ∧ Y ⊆ Y') ∧
    (∀ (X X' : Finset ι) (Y Y' : Finset κ), IsExtremeStable A r c X Y →
      IsExtremeStable A r c X' Y' →
      ((∑ i ∈ X, r i, ∑ j ∈ Y, c j) : ℝ × ℝ) = (∑ i ∈ X', r i, ∑ j ∈ Y', c j) →
      X = X' ∧ Y = Y') := by sorry

end SinkhornHall.Supplement
