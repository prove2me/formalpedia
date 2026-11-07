-- Prove2me | Theorems.Thm_SelfScaledIPM_ShortStep_lemma_6_3_qs_bound
-- name    : SelfScaledIPM.ShortStep.lemma_6_3_qs_bound
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-11-06T07:56:01.462388+00:00
-- url     : https://prove2.me/theorems/e1266528-7ac6-4b75-acfc-bb06c1432f9c
-- title:
--   Lemma 6.3 (dual estimate), p. 28 — if η = ϵ₊/(1 − δ) < 1 then the dual step satisfies ‖q_s‖_s ≤ η
-- statement:
--   Let $K$ be a self-scaled cone with $\nu$-self-scaled barrier $F$ and conjugate barrier $F_*$, and let $A$ be surjective. Let $(x,y,s)\in N(\beta)$ with $0<\beta<1$. Fix $0<\kappa<1$, put $\mu_+=(1-\kappa/\sqrt\nu)\,\mu(x,s)$ (6.4), let $w$ be the scaling point of $(x,s)$ (so $F''(w)x=s$), and let $(q_x,q_y,q_s)$ solve the short-step system (6.7):
--   $$F''(w)q_x+q_s=s+\mu_+F'(x),\qquad Aq_x=0,\qquad A^*q_y+q_s=0.$$
--   With $\delta=\lambda_\infty(x,s)$ and $\epsilon_+=\|s/\mu_++F'(x)\|_x$, suppose $\eta=\epsilon_+/(1-\delta)<1$ (6.11). Then the dual component of the step satisfies
--   $$\|q_s\|_s=\langle F_*''(s)q_s,q_s\rangle^{1/2}\le\eta .$$
--
--   This is the second inequality of Lemma 6.3. The paper proves the first one, $\|q_x\|_x\le\eta$, using Lemma 3.13 and the orthogonality $\langle q_s,q_x\rangle=0$, and then says "similarly $\|q_s\|_s\le\eta$". The dual argument uses the second half of (3.22), $F_*''(t)=[F''(w)]^{-1}$ with $t=-F'(w)$, the symmetric form $q_x+F_*''(t)q_s=x+\mu_+F_*'(s)$ of (6.7), and (3.3).
--
--   **Formalization note.** $E^*$ is identified with $E$, and $\|\cdot\|_s$ is `lnorm (conj K F) s`, the local norm at the dual point $s\in\operatorname{int}K^*$ of the dual vector $q_s$. The hypotheses are exactly those of the platform statement of Lemma 6.3.
-- source:
--   Nesterov & Todd, Primal-dual interior-point methods for self-scaled cones, SIAM J. Optim. 8 (1998) 324–364 (authors' copy, Cornell eCommons), p. 28, Lemma 6.3, second inequality ‖q_s‖_s ≤ η ("and similarly ‖q_s‖_s ≤ η" in the proof)

import Mathlib
import Definitions.Def_dualCone
import Definitions.Def_SelfScaledIPM_ShortStep_Setting
import Definitions.Def_SelfScaledIPM_ShortStep_Measures

open scoped InnerProductSpace

namespace SelfScaledIPM.ShortStep

/-- **Lemma 6.3, dual estimate** (p. 28): under the hypotheses of Lemma 6.3 —
`(x, y, s) ∈ N(β)`, `β, κ ∈ (0, 1)`, `µ₊ = (1 − κ/√ν)µ(x, s)` (6.4), `w` the scaling point of
`(x, s)`, `(q_x, q_y, q_s)` a solution of (6.7), and `η = ϵ₊/(1 − δ) < 1` (6.11) — the dual
step satisfies `‖q_s‖_s ≤ η`, the norm being the local norm of `q_s ∈ E*` at the dual point
`s ∈ int K*`, i.e. `⟨F*''(s) q_s, q_s⟩^{1/2}` (`lnorm (conj K F) s q_s`). -/
theorem lemma_6_3_qs_bound {n m : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsProperCone K)
    (F : EuclideanSpace ℝ (Fin n) → ℝ) (ν : ℝ) (hν : 1 ≤ ν) (hF : IsSelfScaledBarrier K F ν)
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m)) (hA : Function.Surjective A)
    (b : EuclideanSpace ℝ (Fin m)) (c : EuclideanSpace ℝ (Fin n))
    (β κ : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) (hκ0 : 0 < κ) (hκ1 : κ < 1)
    (x : EuclideanSpace ℝ (Fin n)) (y : EuclideanSpace ℝ (Fin m)) (s : EuclideanSpace ℝ (Fin n))
    (hN : InN K F A b c ν β x y s)
    (w : EuclideanSpace ℝ (Fin n)) (hw : IsScalingPoint K F x s w)
    (qx : EuclideanSpace ℝ (Fin n)) (qy : EuclideanSpace ℝ (Fin m)) (qs : EuclideanSpace ℝ (Fin n))
    (hq : IsShortStepDir F A x s w (muPlus ν κ x s) qx qy qs)
    (hη : eta K F ν κ x s < 1) :
    lnorm (conj K F) s qs ≤ eta K F ν κ x s := by sorry

end SelfScaledIPM.ShortStep
