-- Prove2me | Theorems.Thm_SelfScaledIPM_FuncProx_lemma_5_4
-- name    : SelfScaledIPM.FuncProx.lemma_5_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:22:01.408193+00:00
-- url     : https://prove2.me/theorems/032b9a2c-20d4-40fe-94c9-49099461dd5c
-- title:
--   Lemma 5.4, p. 23 — bounds (5.12)–(5.14) on ⟨F′(x), p(x, s)⟩ and ‖p(x, s)‖_x
-- statement:
--   In the setting of Theorem 5.3, with $p=p(x,s)=-\tfrac12[F''(x)]^{-1}F'''(x)[p_x,[F''(w)]^{-1}p_s]$ and all measures at $(x,s)$:
--   $$\langle F'(x),p\rangle\le2(1+\lambda^+_\infty)\sqrt{\gamma_G}\;|p_x|_x\cdot\|p_s\|_s, \tag{5.12}$$
--   $$\langle F'(x),p\rangle\le\nu(1+\gamma_\infty)\sqrt{\gamma_F}, \tag{5.13}$$
--   $$\|p\|_x\le|p_x|_x\,\|p_s\|_s\le\tfrac12\nu(1+\gamma_\infty). \tag{5.14}$$
--   Here $\|p_s\|_s$ is the local norm of $F_*$ at $s$ and $|p_x|_x$ is relative to $K$ at $x$.
--
--   Combined with (5.8) these bounds give the lower bounds (7.2)–(7.3) on the predictor step of Algorithm 7.1.
-- source:
--   Nesterov & Todd, Primal-dual interior-point methods for self-scaled cones, SIAM J. Optim. 8 (1998) 324–364 (authors' copy, Cornell eCommons), p. 23, Lemma 5.4, (5.12)–(5.14)

import Mathlib
import Definitions.Def_dualCone
import Definitions.Def_SelfScaledIPM_FuncProx_Setting
import Definitions.Def_SelfScaledIPM_FuncProx_Measures
import Definitions.Def_SelfScaledIPM_FuncProx_Directions

open scoped InnerProductSpace

namespace SelfScaledIPM.FuncProx

/-- **Lemma 5.4** (p. 23). In the setting of Theorem 5.3, with
`p = p(x, s) = −½[F''(x)]⁻¹F'''(x)[p_x, [F''(w)]⁻¹p_s]`:
(5.12) `⟨F'(x), p⟩ ≤ 2(1 + λ⁺_∞) √γ_G · |p_x|_x · ‖p_s‖_s`;
(5.13) `⟨F'(x), p⟩ ≤ ν(1 + γ_∞) √γ_F`;
(5.14) `‖p‖_x ≤ |p_x|_x ‖p_s‖_s ≤ ½ ν (1 + γ_∞)`; measures at `(x, s)`, `‖p_s‖_s` the local norm of
`F*` at `s`. -/
theorem lemma_5_4
    {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) (hK : SelfScaledIPM.ShortStep.IsProperCone K)
    (F : EuclideanSpace ℝ (Fin n) → ℝ) (ν : ℝ) (hν : 1 ≤ ν) (hF : SelfScaledIPM.ShortStep.IsSelfScaledBarrier K F ν)
    {m : ℕ} (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (hA : Function.Surjective A) (b : EuclideanSpace ℝ (Fin m)) (c : EuclideanSpace ℝ (Fin n))
    (x : EuclideanSpace ℝ (Fin n)) (y : EuclideanSpace ℝ (Fin m)) (s : EuclideanSpace ℝ (Fin n))
    (hfeas : IsStrictlyFeasible K A b c x y s)
    (w : EuclideanSpace ℝ (Fin n)) (hw : SelfScaledIPM.ShortStep.IsScalingPoint K F x s w)
    (px : EuclideanSpace ℝ (Fin n)) (py : EuclideanSpace ℝ (Fin m)) (ps : EuclideanSpace ℝ (Fin n))
    (hp : IsAffineScalingDir A F s w px py ps)
    (z p : EuclideanSpace ℝ (Fin n)) (hz : SelfScaledIPM.ShortStep.hess F w z = ps) (hpdef : SelfScaledIPM.ShortStep.hess F x p = -(1 / 2 : ℝ) • third F x px z) :
    ⟪gradient F x, p⟫_ℝ ≤ 2 * (1 + lambdaPlusInf K F ν x s) * Real.sqrt (gammaG K F ν x s) *
      SelfScaledIPM.ShortStep.absn K x px * SelfScaledIPM.ShortStep.lnorm (SelfScaledIPM.ShortStep.conj K F) s ps ∧
    ⟪gradient F x, p⟫_ℝ ≤ ν * (1 + gammaInf K F ν x s) * Real.sqrt (gammaF K F ν x s) ∧
    SelfScaledIPM.ShortStep.lnorm F x p ≤ SelfScaledIPM.ShortStep.absn K x px * SelfScaledIPM.ShortStep.lnorm (SelfScaledIPM.ShortStep.conj K F) s ps ∧
    SelfScaledIPM.ShortStep.absn K x px * SelfScaledIPM.ShortStep.lnorm (SelfScaledIPM.ShortStep.conj K F) s ps ≤ (1 / 2 : ℝ) * ν * (1 + gammaInf K F ν x s) := by sorry

end SelfScaledIPM.FuncProx
