-- Prove2me | Theorems.Thm_SmoothCCP_Feasibility_net_claim
-- name    : SmoothCCP.Feasibility.net_claim
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T12:43:13.283142+00:00
-- url     : https://prove2.me/theorems/b2f68a53-8c1f-4cc5-bfa3-c465261047b0
-- title:
--   Proof of Theorem 3.13, p. 14 — each level set X_j has a finite Z_j ⊆ X_j, |Z_j| ≤ ⌈2LD/t⌉ⁿ, that is a t/L-net in ‖·‖∞
-- statement:
--   Let $X\subseteq\mathbb R^n$ be closed and bounded with sup-norm diameter at most $D>0$, i.e. $\|x-y\|_\infty\le D$ for all $x,y\in X$, and let $L>0$, $t>0$ and $\beta>0$. Put $J=\lceil 1/\beta\rceil$ and slice $X$ by the value of the true cdf $F(0;x)=\mathbb P(C(x,\xi)\le0)$:
--   $$X_j=\Bigl\{x\in X \Bigm| \tfrac{j-1}{J}\le F(0;x)<\tfrac jJ\Bigr\}\ (j=1,\dots,J-1),\qquad X_J=\Bigl\{x\in X\Bigm|\tfrac{J-1}{J}\le F(0;x)\le 1\Bigr\}.$$
--   Then for each $j\in\{1,\dots,J\}$ there exists a finite set $Z_j\subseteq X_j$ with
--   $$|Z_j|\le\lceil 2LD/t\rceil^n$$
--   such that every $x\in X_j$ has some $z\in Z_j$ with $\|x-z\|_\infty\le t/L$.
--
--   This is the covering step of the proof of Theorem 3.13: it replaces the infinite region by finitely many representatives whose true cdf values differ from those they represent by at most $1/J\le\beta$.
--
--   **Formalization Note** The standing hypotheses of §3 (closed $X$, measurable $C(x,\cdot)$, Assumption 3.1) are kept; $F$ only enters through the definition of $X_j$. The claim is geometric, so $L$ is an arbitrary positive number here (in the proof it is the Lipschitz constant of Assumption 3.12), which makes the statement slightly more general than its use. $D$ is an upper bound on the sup-norm diameter and must be positive: for a one-point $X$ and $n\ge1$, $\lceil 0\rceil^n=0$ would make the claim false.
-- source:
--   Peña-Ordieres, Luedtke, Wächter, Solving chance-constrained problems via a smooth sample-based nonlinear approximation, arXiv:1905.07377v2, proof of Theorem 3.13, p. 14, "for each j there exists a finite set Z_j ⊆ X_j such that |Z_j| ≤ ⌈2LD/t⌉ⁿ …"

import Mathlib
import Definitions.Def_SmoothCCP_Feasibility_Setting
open MeasureTheory

namespace SmoothCCP.Feasibility

theorem net_claim {n : ℕ} {Ξ : Type} [MeasurableSpace Ξ] (Pξ : Measure Ξ) [IsProbabilityMeasure Pξ]
    (C : (Fin n → ℝ) → Ξ → ℝ) (X : Set (Fin n → ℝ)) (hX : IsClosed X)
    (hC : ∀ x ∈ X, Measurable (C x)) (hcont : ∀ x ∈ X, ∀ y : ℝ, Pξ {s | C x s = y} = 0)
    (D : ℝ) (hD : 0 < D) (hdiam : ∀ x ∈ X, ∀ y ∈ X, ‖x - y‖ ≤ D)
    (L t β : ℝ) (hL : 0 < L) (ht : 0 < t) (hβ : 0 < β) :
    let J : ℕ := ⌈1 / β⌉₊
    ∀ j ∈ Finset.Icc 1 J,
      let Xj : Set (Fin n → ℝ) :=
        if j < J then
          {x | x ∈ X ∧ ((j : ℝ) - 1) / (J : ℝ) ≤ cdf Pξ C 0 x ∧ cdf Pξ C 0 x < (j : ℝ) / (J : ℝ)}
        else
          {x | x ∈ X ∧ ((J : ℝ) - 1) / (J : ℝ) ≤ cdf Pξ C 0 x ∧ cdf Pξ C 0 x ≤ 1}
      ∃ Z : Finset (Fin n → ℝ), (↑Z : Set (Fin n → ℝ)) ⊆ Xj ∧
        Z.card ≤ ⌈2 * L * D / t⌉₊ ^ n ∧ ∀ x ∈ Xj, ∃ z ∈ Z, ‖x - z‖ ≤ t / L := by sorry

end SmoothCCP.Feasibility
