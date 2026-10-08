-- Prove2me | Theorems.Thm_SkutellaCQP_NoRel_cqp_psd
-- name    : SkutellaCQP.NoRel.cqp_psd
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-07T00:06:06.050844+00:00
-- url     : https://prove2.me/theorems/457417be-8dd3-471c-84a9-839a755fa422
-- title:
--   Proof of Lemma 2.4, p. 11 — D + diag(c) is positive semidefinite for every instance
-- statement:
--   For every instance of $R\,|\,|\sum w_jC_j$ (processing times $p_{ij}>0$, weights $w_j\ge 0$), the symmetric matrix
--
--   $$
--   D+\operatorname{diag}(c)
--   $$
--
--   is positive semidefinite, where $c_{ij}=w_jp_{ij}$ and $D$ is the matrix of (4).
--
--   This is the case $\gamma=\tfrac12$ of Lemma 2.4 that its proof establishes, and the reason the objective of (CQP), $\tfrac12c^Ta+\tfrac12a^T(D+\operatorname{diag}(c))a$, is convex.
--
--   **Formalization Note** Positive semidefiniteness is Mathlib's `Matrix.PosSemidef` (Hermitian, i.e. symmetric over $\mathbb R$, with $x^TMx\ge 0$ for all $x$).
-- source:
--   Skutella, Convex quadratic and semidefinite programming relaxations in scheduling, J. ACM 48 (2001), p. 11, §2.2, proof of Lemma 2.4

import Mathlib
import Definitions.Def_SkutellaCQP_NoRel_Setting

namespace SkutellaCQP.NoRel

/-- Proof of Lemma 2.4 (p. 11): for every instance, `D + diag(c)` is positive semidefinite. -/
theorem cqp_psd {m n : ℕ} (p : Fin m → Fin n → ℝ) (w : Fin n → ℝ)
    (hp : ∀ i j, 0 < p i j) (hw : ∀ j, 0 ≤ w j) :
    (Dmat p w + Matrix.diagonal (cvec p w)).PosSemidef := by sorry

end SkutellaCQP.NoRel
