-- Prove2me | Theorems.Thm_SelfScaledIPM_FuncProx_lemma_5_2
-- name    : SelfScaledIPM.FuncProx.lemma_5_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:21:50.27499+00:00
-- url     : https://prove2.me/theorems/bba695e5-83d9-460e-81b3-f36ddd2298bd
-- title:
--   Lemma 5.2, p. 21 — affine-scaling direction: (5.4)–(5.6) and max{|p_x|_x, |p_s|_s} ≥ 1
-- statement:
--   Let $K$ be a proper cone with a $\nu$-self-scaled barrier $F$, $A$ surjective, $(x,y,s)$ strictly feasible with scaling point $w$, and let $(p_x,p_y,p_s)$ be the affine-scaling direction. Then
--   $$\langle s,p_x\rangle+\langle p_s,x\rangle=\langle s,x\rangle, \tag{5.4}$$
--   $$\langle F'(x),p_x\rangle+\langle p_s,F_*'(s)\rangle=-\nu, \tag{5.5}$$
--   $$\|p_x\|_w^2+\|p_s\|_w^2=\langle s,x\rangle, \tag{5.6}$$
--   $$\bar\sigma(x,s):=\max\{|p_x|_x,|p_s|_s\}\ge1. \tag{5.7}$$
--   Here $\|p_s\|_w$ is the dual local norm of $F$ at $w$, $|p_x|_x$ is relative to $K$ at $x$ and $|p_s|_s$ relative to $K^*$ at $s$.
--
--   These identities show that a full affine-scaling step would annihilate the duality gap and hence leave the cone; they feed into Theorem 5.3 and Lemma 5.4.
-- source:
--   Nesterov & Todd, Primal-dual interior-point methods for self-scaled cones, SIAM J. Optim. 8 (1998) 324–364 (authors' copy, Cornell eCommons), p. 21, Lemma 5.2, (5.4)–(5.7)

import Mathlib
import Definitions.Def_dualCone
import Definitions.Def_SelfScaledIPM_FuncProx_Setting
import Definitions.Def_SelfScaledIPM_FuncProx_Measures
import Definitions.Def_SelfScaledIPM_FuncProx_Directions

open scoped InnerProductSpace

namespace SelfScaledIPM.FuncProx

/-- **Lemma 5.2** (p. 21). For a strictly feasible `(x, y, s)` with scaling point `w` and
affine-scaling direction `(p_x, p_y, p_s)`:
(5.4) `⟨s, p_x⟩ + ⟨p_s, x⟩ = ⟨s, x⟩`; (5.5) `⟨F'(x), p_x⟩ + ⟨p_s, F*'(s)⟩ = −ν`;
(5.6) `‖p_x‖²_w + ‖p_s‖²_w = ⟨s, x⟩`; (5.7) `max {|p_x|_x, |p_s|_s} ≥ 1`. -/
theorem lemma_5_2
    {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) (hK : SelfScaledIPM.ShortStep.IsProperCone K)
    (F : EuclideanSpace ℝ (Fin n) → ℝ) (ν : ℝ) (hν : 1 ≤ ν) (hF : SelfScaledIPM.ShortStep.IsSelfScaledBarrier K F ν)
    {m : ℕ} (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (hA : Function.Surjective A) (b : EuclideanSpace ℝ (Fin m)) (c : EuclideanSpace ℝ (Fin n))
    (x : EuclideanSpace ℝ (Fin n)) (y : EuclideanSpace ℝ (Fin m)) (s : EuclideanSpace ℝ (Fin n))
    (hfeas : IsStrictlyFeasible K A b c x y s)
    (w : EuclideanSpace ℝ (Fin n)) (hw : SelfScaledIPM.ShortStep.IsScalingPoint K F x s w)
    (px : EuclideanSpace ℝ (Fin n)) (py : EuclideanSpace ℝ (Fin m)) (ps : EuclideanSpace ℝ (Fin n))
    (hp : IsAffineScalingDir A F s w px py ps) :
    ⟪s, px⟫_ℝ + ⟪ps, x⟫_ℝ = ⟪s, x⟫_ℝ ∧
    ⟪gradient F x, px⟫_ℝ + ⟪ps, gradient (SelfScaledIPM.ShortStep.conj K F) s⟫_ℝ = -ν ∧
    SelfScaledIPM.ShortStep.lnorm F w px ^ 2 + SelfScaledIPM.ShortStep.dnorm F w ps ^ 2 = ⟪s, x⟫_ℝ ∧
    1 ≤ max (SelfScaledIPM.ShortStep.absn K x px) (SelfScaledIPM.ShortStep.absn (ConvexOptimization.dualCone K) s ps) := by sorry

end SelfScaledIPM.FuncProx
