-- Prove2me | Theorems.Thm_SelfScaledIPM_FuncProx_lemma_5_6
-- name    : SelfScaledIPM.FuncProx.lemma_5_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:22:11.988508+00:00
-- url     : https://prove2.me/theorems/27e42c38-6c95-443d-863e-ee99a32a2a30
-- title:
--   Lemma 5.6, p. 24 — centering direction: (5.20)–(5.23) and w-orthogonality (5.24) to the affine-scaling direction
-- statement:
--   Let $K$ be a proper cone with a $\nu$-self-scaled barrier $F$, $A$ surjective, $(x,y,s)$ strictly feasible with scaling point $w$, $(d_x,d_y,d_s)$ the centering direction and $(p_x,p_y,p_s)$ the affine-scaling direction. Then, with the measures at $(x,s)$ and $\mu=\mu(x,s)$,
--   $$\langle s,d_x\rangle+\langle d_s,x\rangle=0, \tag{5.20}$$
--   $$\langle F'(x),d_x\rangle+\langle d_s,F_*'(s)\rangle=\gamma_G, \tag{5.21}$$
--   $$\|d_x\|_w^2+\|d_s\|_w^2=\mu\,\gamma_G, \tag{5.22}$$
--   $$\|d_x\|_x^2+\|d_s\|_s^2\le\gamma_G(1+\gamma_\infty), \tag{5.23}$$
--   and the two directions are orthogonal in the metric defined by $w$:
--   $$\langle F''(w)p_x,d_x\rangle+\langle d_s,[F''(w)]^{-1}p_s\rangle=0. \tag{5.24}$$
--
--   By (5.20) the centering direction keeps the duality gap constant, which is why the corrector phase of Algorithm 7.1 does not undo the predictor's gap reduction.
--
--   **Formalization Note** $[F''(w)]^{-1}p_s$ is given by its defining equation $F''(w)z=p_s$. The affine-scaling direction, needed only for (5.24), is a hypothesis of the whole item; it always exists.
-- source:
--   Nesterov & Todd, Primal-dual interior-point methods for self-scaled cones, SIAM J. Optim. 8 (1998) 324–364 (authors' copy, Cornell eCommons), p. 24, Lemma 5.6, (5.20)–(5.24)

import Mathlib
import Definitions.Def_dualCone
import Definitions.Def_SelfScaledIPM_FuncProx_Setting
import Definitions.Def_SelfScaledIPM_FuncProx_Measures
import Definitions.Def_SelfScaledIPM_FuncProx_Directions

open scoped InnerProductSpace

namespace SelfScaledIPM.FuncProx

/-- **Lemma 5.6** (p. 24). For a strictly feasible `(x, y, s)` with scaling point `w`, centering
direction `(d_x, d_y, d_s)` and affine-scaling direction `(p_x, p_y, p_s)` (with
`z = [F''(w)]⁻¹p_s`):
(5.20) `⟨s, d_x⟩ + ⟨d_s, x⟩ = 0`; (5.21) `⟨F'(x), d_x⟩ + ⟨d_s, F*'(s)⟩ = γ_G`;
(5.22) `‖d_x‖²_w + ‖d_s‖²_w = µ γ_G`; (5.23) `‖d_x‖²_x + ‖d_s‖²_s ≤ γ_G (1 + γ_∞)`;
(5.24) `⟨F''(w)p_x, d_x⟩ + ⟨d_s, [F''(w)]⁻¹p_s⟩ = 0`. -/
theorem lemma_5_6
    {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) (hK : SelfScaledIPM.ShortStep.IsProperCone K)
    (F : EuclideanSpace ℝ (Fin n) → ℝ) (ν : ℝ) (hν : 1 ≤ ν) (hF : SelfScaledIPM.ShortStep.IsSelfScaledBarrier K F ν)
    {m : ℕ} (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (hA : Function.Surjective A) (b : EuclideanSpace ℝ (Fin m)) (c : EuclideanSpace ℝ (Fin n))
    (x : EuclideanSpace ℝ (Fin n)) (y : EuclideanSpace ℝ (Fin m)) (s : EuclideanSpace ℝ (Fin n))
    (hfeas : IsStrictlyFeasible K A b c x y s)
    (w : EuclideanSpace ℝ (Fin n)) (hw : SelfScaledIPM.ShortStep.IsScalingPoint K F x s w)
    (dx : EuclideanSpace ℝ (Fin n)) (dy : EuclideanSpace ℝ (Fin m)) (ds : EuclideanSpace ℝ (Fin n))
    (hd : IsCenteringDir A F ν x s w dx dy ds)
    (px : EuclideanSpace ℝ (Fin n)) (py : EuclideanSpace ℝ (Fin m)) (ps : EuclideanSpace ℝ (Fin n))
    (hp : IsAffineScalingDir A F s w px py ps)
    (z : EuclideanSpace ℝ (Fin n)) (hz : SelfScaledIPM.ShortStep.hess F w z = ps) :
    ⟪s, dx⟫_ℝ + ⟪ds, x⟫_ℝ = 0 ∧
    ⟪gradient F x, dx⟫_ℝ + ⟪ds, gradient (SelfScaledIPM.ShortStep.conj K F) s⟫_ℝ = gammaG K F ν x s ∧
    SelfScaledIPM.ShortStep.lnorm F w dx ^ 2 + SelfScaledIPM.ShortStep.dnorm F w ds ^ 2 = SelfScaledIPM.ShortStep.mu ν x s * gammaG K F ν x s ∧
    SelfScaledIPM.ShortStep.lnorm F x dx ^ 2 + SelfScaledIPM.ShortStep.lnorm (SelfScaledIPM.ShortStep.conj K F) s ds ^ 2 ≤
      gammaG K F ν x s * (1 + gammaInf K F ν x s) ∧
    ⟪SelfScaledIPM.ShortStep.hess F w px, dx⟫_ℝ + ⟪ds, z⟫_ℝ = 0 := by sorry

end SelfScaledIPM.FuncProx
