-- Prove2me | Theorems.Thm_RollingProbeQN_Convex_lemma_D_12
-- name    : RollingProbeQN.Convex.lemma_D_12
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:19:46.606352+00:00
-- url     : https://prove2.me/theorems/f02f359c-b122-4f50-b1fb-dd336d66cc2f
-- title:
--   Lemma D.12 — one grouped gradient difference recovers a group of Hessian columns
-- statement:
--   Let $f$ be twice continuously differentiable with $L_2$-Lipschitz Hessian and $\operatorname{supp}H(x)\subseteq\mathcal S$ for every $x$, and let $g$ be a group of a structurally orthogonal partition for $\mathcal S$. For $x\in\mathbb R^d$ and $\tau>0$ let $w=(\nabla f(x+\tau v_g)-\nabla f(x))/\tau$. Then
--
--   $$\Big(\sum_{j\in g}\|P_jw-H(x)e_j\|^2\Big)^{1/2}\ \le\ \frac{L_2\,\tau\,|g|}{2}.$$
--
--   So one gradient difference along $v_g$ recovers all columns of the group, and a matrix with pattern $\mathcal S$ is formed from $\chi+1$ gradients.
--
--   Differences from the source:
--   - encoding: a partition g₁, …, g_χ of [d] → a surjective map grp : Fin d → Fin χ with 0 < χ; reason: a partition has no empty block (reading R7)
-- source:
--   Mokhtari, Patitucci, Improved Gradient Complexity for Quasi-Newton Proximal Extragradient Methods via Certified Curvature Reuse, arXiv:2610.40608, Lemma D.12, pp. 41–42

import Mathlib
import Definitions.Def_RollingProbeQN_Convex_hess
import Definitions.Def_RollingProbeQN_Convex_IsStructOrthPartition
import Definitions.Def_RollingProbeQN_Convex_colProj
import Definitions.Def_RollingProbeQN_Convex_groupVec
import Definitions.Def_RollingProbeQN_Convex_groupCard

namespace RollingProbeQN.Convex

/-- **Lemma D.12 (Grouped finite differences).**
Mokhtari, Patitucci, *Improved Gradient Complexity for Quasi-Newton Proximal Extragradient
Methods via Certified Curvature Reuse*, arXiv:2610.40608, Lemma D.12, pp. 41–42: "Let `f` be twice continuously differentiable with `L2`-Lipschitz
Hessian and `supp H(x) ⊆ S` for every `x`, let `g` be a group of a structurally orthogonal
partition for `S`, `x ∈ R^d` and `τ > 0`, and let `w = (∇f(x + τv_g) − ∇f(x))/τ`. Then
`(∑_{j∈g} ‖P_j w − H(x)e_j‖²)^{1/2} ≤ L2τ|g|/2`."

**Formalization Note.** The group is `g : Fin χ`, its columns are `{j | grp j = g}`; `v_g` is
`groupVec grp g` and `|g|` is `groupCard grp g`. -/
theorem lemma_D_12 {d χ : ℕ} {f : EuclideanSpace ℝ (Fin d) → ℝ} {L₂ : ℝ}
    {S : Set (Fin d × Fin d)} {grp : Fin d → Fin χ} (hf : ContDiff ℝ 2 f)
    (hL : ∀ x y : EuclideanSpace ℝ (Fin d), ‖hess f x - hess f y‖ ≤ L₂ * ‖x - y‖)
    (hsupp : ∀ (x : EuclideanSpace ℝ (Fin d)) (i j : Fin d), (i, j) ∉ S →
      inner ℝ (EuclideanSpace.single i (1 : ℝ)) (hess f x (EuclideanSpace.single j (1 : ℝ))) = 0)
    (hpart : IsStructOrthPartition S grp) (g : Fin χ) (x : EuclideanSpace ℝ (Fin d)) (τ : ℝ)
    (hτ : 0 < τ) :
    Real.sqrt (∑ j ∈ Finset.univ.filter (fun j => grp j = g),
        ‖colProj S j (τ⁻¹ • (gradient f (x + τ • groupVec grp g) - gradient f x))
          - hess f x (EuclideanSpace.single j (1 : ℝ))‖ ^ 2)
      ≤ L₂ * τ * (groupCard grp g : ℝ) / 2 := by sorry

end RollingProbeQN.Convex
