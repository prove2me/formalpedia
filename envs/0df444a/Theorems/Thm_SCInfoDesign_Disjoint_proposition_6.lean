-- Prove2me | Theorems.Thm_SCInfoDesign_Disjoint_proposition_6
-- name    : SCInfoDesign.Disjoint.proposition_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T01:18:49.423554+00:00
-- url     : https://prove2.me/theorems/050a29af-b78d-4dfb-985c-c3204003d781
-- title:
--   Proposition 6, p. 37 — the supplier's optimal quantity with disjoint supports, and the optimal interval [b₁, a₀] at p = 1 − ξ
-- statement:
--   Let $D_0\sim U[a_0,b_0]$ and $D_1\sim U[a_1,b_1]$ with $a_0<b_0$, $a_1<b_1$, $0\le a_0$, $0\le a_1$ and disjoint supports $b_1<a_0$, and let $0<\xi<1$. For a belief $p=\mathbb P(\omega=0)$, call $Q$ optimal if it minimizes the supplier's newsvendor cost (2) over $Q\ge0$. Then:
--
--   1. for $0\le p<1-\xi$, the unique optimal quantity is
--   $$Q^*_p=\frac{\xi(b_1-a_1)}{1-p}+a_1;$$
--   2. for $1-\xi<p\le1$, the unique optimal quantity is
--   $$Q^*_p=\frac{(\xi-1+p)(b_0-a_0)}{p}+a_0;$$
--   3. at $p=1-\xi$, the optimal quantities are exactly the points of the interval $[b_1,a_0]$.
--
--   This is the supplier's best response in every posterior; it feeds the closed form (C.9) of the retailer's cost $K_{DS}$.
--
--   **Formalization Note** The paper's Proposition 6 assigns the boundary belief $p=1-\xi$ to the first formula, which gives $Q=b_1$. There the mixture c.d.f. (C.7) equals $\xi$ on all of $[b_1,a_0]$, so every point of that interval is optimal; part 3 states this, and it contains the printed value $b_1$. The hypotheses $a_0<b_0$, $a_1<b_1$, $0\le a_1$ and $0<\xi<1$ are the paper's implicit standing assumptions (nondegenerate laws, nonnegative demand, positive unit costs); $0\le a_0$ follows from the others here and is kept for uniformity with the series.
-- source:
--   Candogan, Gurkan, The Value of Information Design in Supply Chain Management, SSRN 4378997 (preprint), p. 37, Proposition 6, (C.6), (C.7)

import Mathlib
import Definitions.Def_BiconvexProg_BranchBound_convexEnvelope
import Definitions.Def_SCInfoDesign_Disjoint_Setting

namespace SCInfoDesign.Disjoint

/-- Proposition 6 (p. 37), with the boundary belief `p = 1 - ξ` stated separately: there the
optimal set of (2) is the whole interval `[b₁, a₀]`, whose left end is the printed value. -/
theorem proposition_6 (P : Params) (hab₀ : P.a₀ < P.b₀) (hab₁ : P.a₁ < P.b₁) (ha₀ : 0 ≤ P.a₀) (ha₁ : 0 ≤ P.a₁)
    (hξ₀ : 0 < P.ξ) (hξ₁ : P.ξ < 1) (hdisj : P.b₁ < P.a₀) :
    (∀ p ∈ Set.Ico (0 : ℝ) (1 - P.ξ), ∀ Q : ℝ,
      P.IsOptimalQuantity p Q ↔ Q = P.ξ * (P.b₁ - P.a₁) / (1 - p) + P.a₁) ∧
    (∀ p ∈ Set.Ioc (1 - P.ξ) 1, ∀ Q : ℝ,
      P.IsOptimalQuantity p Q ↔ Q = (P.ξ - 1 + p) * (P.b₀ - P.a₀) / p + P.a₀) ∧
    (∀ Q : ℝ, P.IsOptimalQuantity (1 - P.ξ) Q ↔ Q ∈ Set.Icc P.b₁ P.a₀) := by sorry

end SCInfoDesign.Disjoint
