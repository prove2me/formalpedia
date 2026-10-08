-- Prove2me | Theorems.Thm_SkutellaCQP_NoRel_zqp_eq_zcqp_add
-- name    : SkutellaCQP.NoRel.zqp_eq_zcqp_add
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-07T00:06:18.394302+00:00
-- url     : https://prove2.me/theorems/89e78182-3b91-4ce9-b8f9-71db5a073071
-- title:
--   Proof of Theorem 2.6, p. 12 — Z_QP(a) = Z_CQP(a) + ½(cᵀa − aᵀdiag(c)a)
-- statement:
--   For every vector $a\in\mathbb R^{mn}$,
--
--   $$
--   Z_{QP}(a)=Z_{CQP}(a)+\tfrac12\bigl(c^Ta-a^T\operatorname{diag}(c)\,a\bigr),
--   $$
--
--   where $Z_{QP}(a)=c^Ta+\tfrac12a^TDa$ is the objective of (QP) and $Z_{CQP}(a)=\tfrac12c^Ta+\tfrac12a^T(D+\operatorname{diag}(c))a$ that of (CQP).
--
--   The identity measures the gap between the expected value of the rounded schedule (which is $Z_{QP}$ by Theorem 2.1) and the value of the convex relaxation; it is the common step of Theorem 2.6 and Lemma 2.8.
-- source:
--   Skutella, Convex quadratic and semidefinite programming relaxations in scheduling, J. ACM 48 (2001), p. 12, §2.3, proof of Theorem 2.6 (displayed equality)

import Mathlib
import Definitions.Def_SkutellaCQP_NoRel_Setting

namespace SkutellaCQP.NoRel

open Matrix

/-- The identity in the proof of Theorem 2.6 (p. 12):
`Z_QP(a) = Z_CQP(a) + ½ (c^T a - a^T diag(c) a)` for every `a ∈ ℝ^{mn}`. -/
theorem zqp_eq_zcqp_add {m n : ℕ} (p : Fin m → Fin n → ℝ) (w : Fin n → ℝ)
    (a : Fin m → Fin n → ℝ) :
    ZQP p w a = ZCQP p w a +
      (1 / 2) * (cvec p w ⬝ᵥ vec a - vec a ⬝ᵥ (Matrix.diagonal (cvec p w) *ᵥ vec a)) := by sorry

end SkutellaCQP.NoRel
