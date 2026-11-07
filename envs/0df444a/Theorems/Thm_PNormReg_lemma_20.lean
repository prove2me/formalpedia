-- Prove2me | Theorems.Thm_PNormReg_lemma_20
-- name    : PNormReg.lemma_20
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:41:32.914112+00:00
-- url     : https://prove2.me/theorems/97bd4074-e4a0-459d-a963-062329f99853
-- title:
--   Lemma 20, p.39 — the row/column estimator of Algorithm 6 is a $\sqrt3$-local estimator
-- statement:
--   Let $q\in(1,2]$, $p=q/(q-1)$, and let $M,c$ be normalized so that $\|M\|_{p,2}+\|c\|_p\le1$, with $M_{i:}\ne0$ or $c_i\ne0$ for each $i$, and $\tau_i=\|M_{i:}\|_2+|c_i|$. Let $\tilde g(x,y)=(\tilde u,\tilde v)$ be the row and column estimators of Algorithm 6 at $(x,y)$. Then $\tilde g$ is a $\sqrt3$-local estimator of the saddle operator $g(x,y)=(M^\top y,c-Mx)$ with respect to the local-norm setup of Lemma 19: for all $z,w\in Z$,
--
--   $$\mathbb E[\tilde g(z)]=g(z),\qquad\mathbb E[\|\tilde g(z)\|_w^2]\le3.$$
--
--   The constant second moment, for each fixed base point, is what removes a dimension factor from the number of iterations.
--
--   Differences from the source:
--   - generalization: M, c normalized by (41) as M/Λ, c/Λ → any M, c with ∥M∥_{p,2} + ∥c∥_p ≤ 1; reason: (41) gives this for (M/Λ, c/Λ) by homogeneity, and p.36 uses only this consequence
--   - encoding: a stochastic estimator → a finite outcome type with weights and values; the two samples are independent; reason: the page gives the two marginals and the second moment splits over ũ and ṽ, so only the marginals matter
-- source:
--   Adil, Bullins, O'Carroll, Sidford, Solving p-norm regression in matrix multiplication time, STOC 2027 submission (manuscript sha256 e335b2fa…), Lemma 20, p.39 (PDF p.40); Definition 6, p.36; normalization, p.36

import Mathlib
import Definitions.Def_PNormReg_SMD

namespace PNormReg

/-- **Lemma 20** with Definition 6, p.39 (PDF p.40).

Adil, Bullins, O'Carroll, Sidford, *Solving p-norm regression in matrix multiplication time*, STOC 2027
submission (manuscript sha256 e335b2fa…).

"Let g̃(x, y) := (ũ, ṽ), where ũ, ṽ are the row/column estimators in Algorithm 6 at (x, y). Then g̃ is a
√3-local estimator of g with respect to the local-norm setup of Lemma 19."

**Formalization Note.** `M`, `c` are the normalized values of Algorithm 6. Normalization is used only
through `∥M∥_{p,2} + ∥c∥_p ≤ 1`, which (41) gives for `(M/Λ, c/Λ)` by homogeneity, and that gives
`∥τ∥_p ≤ 1` (p.36). `τ` is line 2's `∥M_{i:}∥₂ + |c_i|`. -/
theorem lemma_20 {d n : ℕ} (q : ℝ) (hq₁ : 1 < q) (hq₂ : q ≤ 2)
    (M : Matrix (Fin n) (Fin d) ℝ) (c : Fin n → ℝ)
    (hnorm : rowNormP2 (conjExp q) M + lpNorm (conjExp q) c ≤ 1)
    (hne : ∀ i, M i ≠ 0 ∨ c i ≠ 0) :
    LocalNormData.IsLocalEstimator (l2lqSetup q (tauOf M c) : LocalNormData d n) (saddleOp M c)
      (estWeight M) (estValue M c) (Real.sqrt 3) := by sorry

end PNormReg
