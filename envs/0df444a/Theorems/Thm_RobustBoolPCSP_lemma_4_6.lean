-- Prove2me | Theorems.Thm_RobustBoolPCSP_lemma_4_6
-- name    : RobustBoolPCSP.lemma_4_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:21:52.60912+00:00
-- url     : https://prove2.me/theorems/39e3de59-69d9-450d-9e5c-93494587bc91
-- title:
--   Lemma 4.6 (Mod-two rigidity of projectors) — additive $\mathbb F_2$-valued functions of projectors on $\mathbb R^d$, $d\ge5$, are multiples of the rank
-- statement:
--   Let $d\ge5$, and let $\mu$ assign an element of $\mathbb F_2$ to every orthogonal projector on $\mathbb R^d$ such that $\mu(P+Q)=\mu(P)+\mu(Q)$ whenever $PQ=0$. Then there is $c\in\mathbb F_2$ with
--
--   $$\mu(P)=c\cdot\operatorname{rank}(P)\qquad\text{for every projector } P.$$
--
--   No regularity of $\mu$ is assumed. The lemma supplies the non-parity anchor in the proof of Theorem 2.2.
--
--   Differences from the source:
--   - encoding: orthogonal projectors on R^d → real symmetric idempotent d × d matrices; reason: the standard identification
--   - encoding: μ(P + Q) = μ(P) + μ(Q) whenever PQ = 0 → μ R = μ P + μ Q for all projectors P, Q, R with PQ = 0 and R = P + Q; reason: for orthogonal projectors with PQ = 0 the sum P + Q is a projector
-- source:
--   Cai, Jiang, Zou, On Robust Promise CSPs: A Boolean Dichotomy, Sharp Quantitative Bounds, and Soft-Equality Transfer, STOC 2027 submission (manuscript of 2026-11-03, sha256 fd1be0d0624155f00f7a115874a4dadfb7ebb2d4187530c7d0bdd4e1406e8732), §4.2, Lemma 4.6, p.19

import Mathlib

set_option autoImplicit false

namespace RobustBoolPCSP

/-- **Lemma 4.6 (Mod-two rigidity of projectors)**, p.19. Cai, Jiang, Zou, *On Robust Promise CSPs*, STOC 2027 submission (manuscript of 2026-11-03,
sha256 fd1be0d0…).
"Let d ≥ 5, and let μ assign an element of F2 to every orthogonal projector on R^d, such that
μ(P + Q) = μ(P) + μ(Q) whenever PQ = 0. Then there is c ∈ F2 with μ(P) = c rank(P) for every
projector P."

**Formalization Note.** Orthogonal projectors on `ℝ^d` are real symmetric idempotent matrices
`P : Matrix (Fin d) (Fin d) ℝ` (`P.IsHermitian ∧ P * P = P`); `F₂ = ZMod 2`. Additivity is required
for every pair of projectors with `PQ = 0` (then `P + Q` is a projector). No regularity of `μ` is
assumed. -/
theorem lemma_4_6 (d : ℕ) (hd : 5 ≤ d)
    (μ : {P : Matrix (Fin d) (Fin d) ℝ // P.IsHermitian ∧ P * P = P} → ZMod 2)
    (hμ : ∀ P Q R : {P : Matrix (Fin d) (Fin d) ℝ // P.IsHermitian ∧ P * P = P},
      P.1 * Q.1 = 0 → R.1 = P.1 + Q.1 → μ R = μ P + μ Q) :
    ∃ c : ZMod 2, ∀ P, μ P = c * (P.1.rank : ZMod 2) := by sorry

end RobustBoolPCSP
