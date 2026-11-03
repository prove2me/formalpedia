-- Prove2me | Theorems.Thm_ProxFlatIP_lemma_6
-- name    : ProxFlatIP.lemma_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:14:38.312102+00:00
-- url     : https://prove2.me/theorems/dc20dc40-d294-425f-9618-9cc7b38b7c6d
-- title:
--   Lemma 6 — a $d$-face at $y^*$ meets a $(k-d)$-face at $0$
-- statement:
--   Let $A\in\mathbb Z^{m\times n}$ have full column rank, let $y^*\in\mathbb R^n$, let $k:=\dim S(y^*)$, and fix $d\in\{1,\dots,k\}$. There exists a $d$-face of $S(y^*)$ containing $y^*$ that intersects some $(k-d)$-face of $S(y^*)$ containing $0$.
--
--   This generalizes the walk along edges of a spindle in the proof of Cook et al.: it lets a path from $y^*$ to $0$ take a step along a face of any chosen dimension.
--
--   Differences from the source:
--   - generalization: x* ∈ Rⁿ, d = dim S(x*), y* ∈ S(x*) → any y* ∈ Rⁿ; reason: x* and the first d play no role in the statement, and every y* lies in S(y*), so the printed statement is the case y* ∈ S(x*)
-- source:
--   Celaya, Kuhlmann, Paat, Weismantel, Proximity and flatness bounds for linear integer optimization, arXiv:2211.14941v1 [math.OC] (preprint, 27 Nov 2022), https://arxiv.org/abs/2211.14941v1, Lemma 6, p.8

import Mathlib
import Definitions.Def_ProxFlatIP_Spindle

open Matrix

namespace ProxFlatIP

/-- **Lemma 6** (arXiv:2211.14941v1, Lemma 6, p.8). Let `y* ∈ ℝⁿ`, `k := dim S(y*)` and
`d ∈ {1, …, k}`. There is a `d`-face of `S(y*)` containing `y*` that meets some `(k − d)`-face of
`S(y*)` containing `0`.

**Formalization Note.** The paper starts from `x* ∈ ℝⁿ` and `y* ∈ S(x*)`, and calls `dim S(x*)` `d`
before reusing the letter; neither `x*` nor that first `d` plays any role, so the statement is for
every `y*`. `k − d` is not truncated because `d ≤ k`. -/
theorem lemma_6 {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (hA : FullColRank A) (ys : Fin n → ℝ)
    (d : ℕ) (hd1 : 1 ≤ d) (hd2 : d ≤ dimLin (spindle A ys)) :
    ∃ F G : Set (Fin n → ℝ),
      IsDimFace (spindle A ys) d F ∧ ys ∈ F ∧
      IsDimFace (spindle A ys) (dimLin (spindle A ys) - d) G ∧ (0 : Fin n → ℝ) ∈ G ∧
      (F ∩ G).Nonempty := by sorry

end ProxFlatIP
