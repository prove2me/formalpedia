-- Prove2me | Theorems.Thm_PADMPriv_feasibility_A16
-- name    : PADMPriv.feasibility_A16
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T03:08:26.949519+00:00
-- url     : https://prove2.me/theorems/cdefd492-29b1-4495-973a-ff4e3e7f6435
-- title:
--   Proof of Theorem 5.4 (A.16) — every recovered pair $(V\tilde u,U(c-\tilde u))$ is feasible
-- statement:
--   Let $A\in\mathbb R^{m\times p}$ and $B\in\mathbb R^{m\times l}$ have full row rank, $V=A^\top(AA^\top)^{-1}$, $U=B^\top(BB^\top)^{-1}$ and $c\in\mathbb R^m$. Since $AV=BU=I_m$, for every $\tilde u\in\mathbb R^m$ the pair $\tilde x=V\tilde u$, $\tilde y=U(c-\tilde u)$ satisfies
--   $$
--   A\tilde x+B\tilde y=\tilde u+c-\tilde u=c.
--   $$
--   In particular every iterate $(\tilde x_{(k)},\tilde y_{(k)})$ of private PADM, and the stopped output, is feasible for model (1), whatever the noise. This is the exact-feasibility claim in the paper's title.
--
--   Differences from the source:
--   - generalization: the stopped pair (x̃₍K₎, ỹ₍K₎) → every ũ ∈ ℝᵐ; reason: the display uses only AV = BU = I_m; the stopped iterate is one such ũ
-- source:
--   Li–Lai–Weng, Exact Feasibility and Privacy Amplification for Linearly Constrained Optimization, STOC 2027 submission (manuscript sha256 d58edbe0…0f3d), A.16, first display, p.35 (Theorem A, p.3)

import Mathlib
import Definitions.Def_PADMPriv_pinvRight

namespace PADMPriv

/-- The feasibility display of A.16 in Li–Lai–Weng, *Exact Feasibility and Privacy Amplification for Linearly Constrained Optimization*, STOC 2027 submission manuscript (sha256 d58edbe0…0f3d), p.35 (Theorem A, p.3): since
`AV = BU = I_m`, the pair `(x̃, ỹ) = (Vũ, U(c − ũ))` satisfies `Ax̃ + Bỹ = ũ + c − ũ = c`; in
particular every PADM iterate `(x̃₍ₖ₎, ỹ₍ₖ₎)` is feasible for model (1), whatever the noise.

**Formalization Note** Stated for every `ũ ∈ ℝᵐ`, which covers every iterate and every noise
realisation. Full row rank is `rank = m`. -/
theorem feasibility_A16 {m p l : ℕ} (A : Matrix (Fin m) (Fin p) ℝ)
    (B : Matrix (Fin m) (Fin l) ℝ) (hA : A.rank = m) (hB : B.rank = m)
    (c u : EuclideanSpace ℝ (Fin m)) :
    Matrix.toEuclideanLin A (Matrix.toEuclideanLin (pinvRight A) u) +
      Matrix.toEuclideanLin B (Matrix.toEuclideanLin (pinvRight B) (c - u)) = c := by sorry

end PADMPriv
