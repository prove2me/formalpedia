-- Prove2me | Theorems.Thm_RegMT_Classif_proof_3_11_label_split
-- name    : RegMT.Classif.proof_3_11_label_split
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T19:05:24.170372+00:00
-- url     : https://prove2.me/theorems/057b5993-7259-434c-ba5e-312157d10333
-- title:
--   Proof of Theorem 3.11, p. 34 — split the two label choices
-- statement:
--   Fix a sample $(\hat x_i,\hat y_i)$, a classifier $w$, a nonnegative convex Lipschitz loss $L$, and a nonnegative transport price $\lambda$. For the label-switching cost $d$ with $\kappa>0$, the supremum over a feature-label pair splits into its two possible labels:
--   $$\sup_{x,y}\{L(y\langle w,x\rangle)-\lambda d((x,y),(\hat x_i,\hat y_i))\}=\max\left\{\sup_x[L(\hat y_i\langle w,x\rangle)-\lambda\|x-\hat x_i\|],\ \sup_x[L(-\hat y_i\langle w,x\rangle)-\lambda\|x-\hat x_i\|-\kappa\lambda]\right\}.$$
--   This identifies the two constraints that appear in the finite classification program. The suprema are extended-real so unbounded cases remain visible.
-- source:
--   Shafieezadeh-Abadeh, Kuhn & Mohajerin Esfahani, Regularization via Mass Transportation, arXiv:1710.10016v3, p. 34, proof of Theorem 3.11, second equality and following sentence

import Mathlib
import Definitions.Def_RegMT_Classif_Model

namespace RegMT.Classif

open DRLogReg.Reformulation

/-- The label split in the proof of Theorem 3.11, p. 34. -/
theorem proof_3_11_label_split {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    {N : ℕ} (hN : 0 < N) (κ : ℝ) (hκ : 0 < κ)
    (xhat : Fin N → V) (yhat : Fin N → Bool) (L : ℝ → ℝ)
    (hconv : ConvexOn ℝ Set.univ L)
    (hLip : ∃ K : NNReal, LipschitzWith K L)
    (hL0 : ∀ z, 0 ≤ L z)
    (w : V →L[ℝ] ℝ) (i : Fin N) (lam : ℝ) (hlam : 0 ≤ lam) :
    (⨆ ξ : V × Bool,
      ((L (sgn ξ.2 * w ξ.1) -
        lam * featureLabelDist κ ξ (xhat i, yhat i) : ℝ) : EReal)) =
    max
      (⨆ x : V,
        ((L (sgn (yhat i) * w x) - lam * ‖x - xhat i‖ : ℝ) : EReal))
      (⨆ x : V,
        ((L (-(sgn (yhat i) * w x)) -
          lam * ‖x - xhat i‖ - κ * lam : ℝ) : EReal)) := by sorry

end RegMT.Classif
