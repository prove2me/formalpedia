-- Prove2me | Theorems.Thm_StabGen_RKHS_lemma20
-- name    : StabGen.RKHS.lemma20
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T07:56:34.175181+00:00
-- url     : https://prove2.me/theorems/a29c1a63-a669-4de9-8f4c-9d9e9242ac42
-- title:
--   Lemma 20 — regularizer inequality for deletion
-- statement:
--   Let $F$ be a convex class of functions $X\to\mathbb R$, let $c$ be $\sigma$-admissible with respect to $F$, and let $N:F\to\mathbb R_+$ be a regularizer. Fix $\lambda>0$, a sample $S=(z_1,\ldots,z_m)$ and an index $i$. If $f\in F$ minimizes $R_r$ and $f^{\setminus i}\in F$ minimizes $R_r^{\setminus i}$, put $\Delta f=f^{\setminus i}-f$. For every $t\in[0,1]$,
--   $$N(f)-N(f+t\Delta f)+N(f^{\setminus i})-N(f^{\setminus i}-t\Delta f)\le\frac{t\sigma}{\lambda m}|\Delta f(x_i)|.$$
--
--   This is the general regularizer inequality used to obtain the RKHS distance estimate.
--
--   **Formalization Note** The assertion is conditional on the two specified minimizers; the paper assumes existence for every training set. The truncated objective uses the paper's $1/m$ normalization.
-- source:
--   Bousquet & Elisseeff, Stability and Generalization, JMLR 2 (2002), pp. 512–513 (PDF pp. 14–15), Lemma 20, Eq. (21), https://jmlr.org/papers/v2/bousquet02a.html

import Mathlib
import Definitions.Def_StabGen_RKHS_Regularization

namespace StabGen.RKHS

/-- Lemma 20, pp. 512–513, equation (21), for specified minimizers of (19) and (20). -/
theorem lemma20 {X Y : Type*} {m : ℕ} (F : Set (X → ℝ))
    (c : ℝ → Y → ℝ) (σ lam : ℝ) (N : (X → ℝ) → ℝ)
    (S : Fin m → X × Y) (i : Fin m) (f f' : X → ℝ)
    (hF : Convex ℝ F) (hN : ∀ g ∈ F, 0 ≤ N g)
    (hσ : SigmaAdmissible F c σ) (hlam : 0 < lam)
    (hf : f ∈ F) (hf' : f' ∈ F)
    (hmin : ∀ g ∈ F, regRisk c (id : (X → ℝ) → X → ℝ) S lam N f ≤
      regRisk c (id : (X → ℝ) → X → ℝ) S lam N g)
    (hmin' : ∀ g ∈ F, truncRegRisk c (id : (X → ℝ) → X → ℝ) S i lam N f' ≤
      truncRegRisk c (id : (X → ℝ) → X → ℝ) S i lam N g)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    N f - N (f + t • (f' - f)) + N f' - N (f' - t • (f' - f)) ≤
      (t * σ / (lam * (m : ℝ))) * |f' (S i).1 - f (S i).1| := by sorry

end StabGen.RKHS
