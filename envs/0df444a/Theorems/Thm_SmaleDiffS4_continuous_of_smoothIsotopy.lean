-- Prove2me | Theorems.Thm_SmaleDiffS4_continuous_of_smoothIsotopy
-- name    : SmaleDiffS4.continuous_of_smoothIsotopy
-- status  : Proved
-- author  : @SamenHossain
-- created : 2026-10-12T04:24:30.127053+00:00
-- url     : https://prove2.me/theorems/5059f323-782c-4be0-9489-951be01675a0
-- title:
--   Smooth isotopies are continuous paths in the $C^\infty$ topology on $\mathrm{Diff}(D^n\ \mathrm{rel}\ \partial)$
-- statement:
--   Let $n\ge0$ and let $F:\mathbb R\times\mathbb R^n\to\mathbb R^n$ be jointly $C^\infty$. Suppose that for every $t\in[0,1]$ the map $F(t,\cdot)$ equals a diffeomorphism $g_t$ of $\mathbb R^n$ that is the identity outside the open unit ball. Then
--   $$t\longmapsto g_t,\qquad [0,1]\to\mathrm{Diff}(D^n\ \mathrm{rel}\ \partial),$$
--   is continuous for the $C^\infty$ topology.
--
--   The reason is that every spatial derivative $D^k_xF(t,x)$ is jointly continuous, hence uniformly continuous on $[0,1]\times D^n$. Outside the unit ball all $g_t$ coincide with the identity, so the derivatives of $g_t$ converge uniformly on $\mathbb R^n$. This connects the geometric notion of smooth isotopy with path-connectedness in the $C^\infty$ topology.
--
--   **Formalization Note** `DiffDisk n` is the group of smooth diffeomorphisms of $\mathbb R^n$ equal to the identity at every point of norm $\ge1$, with the $C^\infty$ topology of uniform convergence of all derivatives (published definition `SmaleDiffS4_Basic`). A smooth isotopy is a jointly $C^\infty$ map $F:\mathbb R\times\mathbb R^n\to\mathbb R^n$; only $t\in[0,1]$ matters.
-- source:
--   Standard property of the C^∞ topology (e.g. M. W. Hirsch, Differential Topology, Ch. 2, §§1–2); Open Problem Garden, "What is the homotopy type of the group of diffeomorphisms of the 4-sphere?", http://www.openproblemgarden.org/op/what_is_the_homotopy_type_of_the_group_of_diffeomorphisms_of_the_4_sphere; mission "Smale's question: the homotopy type of Diff(S⁴)"

import Mathlib
import Definitions.Def_SmaleDiffS4_Basic

open SmaleDiffS4
open scoped ContDiff

namespace SmaleDiffS4

/-- **Smooth isotopies are paths in the `C^∞` topology.** If `F : ℝ × ℝⁿ → ℝⁿ` is jointly smooth
and `g t` is a diffeomorphism of `Dⁿ` rel boundary equal to `F(t,·)` for every `t ∈ [0,1]`, then
`t ↦ g t` is continuous for the `C^∞` topology on `Diff(Dⁿ rel ∂)`. -/
theorem continuous_of_smoothIsotopy (n : ℕ) (F : ℝ × E n → E n) (hF : ContDiff ℝ ∞ F)
    (g : Set.Icc (0 : ℝ) 1 → DiffDisk n) (hg : ∀ t x, (g t).1 x = F ((t : ℝ), x)) :
    Continuous g := by
  sorry

end SmaleDiffS4
