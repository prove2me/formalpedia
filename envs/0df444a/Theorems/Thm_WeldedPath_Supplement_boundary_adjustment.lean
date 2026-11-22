-- Prove2me | Theorems.Thm_WeldedPath_Supplement_boundary_adjustment
-- name    : WeldedPath.Supplement.boundary_adjustment
-- status  : Open
-- author  : @dmilosch
-- created : 2026-11-22T17:34:56.128806+00:00
-- url     : https://prove2.me/theorems/2d5759a1-bf98-4267-a444-9087f542612b
-- title:
--   Changing the boundary of the welded-tree good space
-- statement:
--   Let $G$ be a valid welded-tree instance of height $n\ge16$, let $2\le\ell\le n-4$, and put $N=2^n$. Let $B$ contain the required boundary $V_{\mathrm{bd}}$, and suppose that both $B$ and the added set $R$ avoid the weld. If $8t|B\cup R|/N\le 1/2$ and $1536(n+1)t^3/N\le 1/2$, then the two orthogonal projectors onto the canonical good subspaces with at most $t$ database records satisfy $$\|\Pi_t(B)-\Pi_t(B\cup R)\|\le64\sqrt{t|R|/N}.$$ The estimate holds in operator norm on the full query and database registers.
-- source:
--   Carolan et al., Algorithmic Wave-Particle Duality: Pathfinding in Welded Trees is Hard, Section 4.3, Lemma 4.10 (explicit-constant boundary adjustment). https://arxiv.org/html/2611.05912v1#S4.SS3

import Definitions.Def_WeldedPath_Supplement_projGood

namespace WeldedPath.Supplement

theorem boundary_adjustment {n l : ℕ} {G : WeldedInstance n}
    (hG : G.IsValid) (hn : 16 ≤ n) (hl : 2 ≤ l) (hln : l ≤ n-4)
    (B R : Finset ℕ) (hB : Vbd n l ⊆ B) (hBw : Disjoint B (Vweld n))
    (hRw : Disjoint R (Vweld n)) (t : ℕ)
    (hsurvive : (2*(t : ℝ))*((B ∪ R).card : ℝ)*(4/(2:ℝ)^n) ≤ 1/2)
    (hcollision : 2*(2*(t : ℝ))^3*(96*((n : ℝ)+1)/(2:ℝ)^n) ≤ 1/2) :
    ‖projGoodB l G B t-projGoodB l G (B ∪ R) t‖ ≤
      64*Real.sqrt ((t : ℝ)*(R.card : ℝ)/(2:ℝ)^n) := by sorry

end WeldedPath.Supplement
