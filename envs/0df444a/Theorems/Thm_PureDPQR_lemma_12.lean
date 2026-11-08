-- Prove2me | Theorems.Thm_PureDPQR_lemma_12
-- name    : PureDPQR.lemma_12
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T07:59:36.26678+00:00
-- url     : https://prove2.me/theorems/7f672a53-9b84-4ea2-94dd-48432cfb2d07
-- title:
--   Lemma 12, p.14 — $\|P-Q\|_{\mathrm{TV}}\le\Pr\{X\ne Y\}$ for every coupling, with equality for some coupling
-- statement:
--   **Lemma 12** (Coupling). Let $P,Q$ be laws on a finite set $Y$. For every coupling $(X,Y)$ of $P$ and $Q$,
--
--   $$\|P-Q\|_{\mathrm{TV}}\le\Pr\{X\ne Y\},$$
--
--   and some coupling attains equality.
--
--   It bounds the total variation in part (iii) of Lemma 14.
--
--   **Formalization Note** A coupling is a law $\mu$ on $Y\times Y$ with marginals $P,Q$, and $\Pr\{X\ne Y\}=\sum_{x\ne y}\mu(x,y)$.
--
--   Differences from the source:
--   - encoding: a coupling (X, Y) of finite laws and Pr{X ≠ Y} → a joint law μ on Y × Y with marginals P, Q, and Σ_{x≠y} μ(x, y); reason: a coupling is determined by its joint law; same quantity
-- source:
--   Zou, Pure Differentially Private Query Release via Laplace Input Smoothing, arXiv:2611.04721 (held version, sha256 69b70d59…), Lemma 12, p.14 (PDF p.15)

import Mathlib
import Definitions.Def_PureDPQR_tvDist

namespace PureDPQR

/-- **Lemma 12** (Coupling [Jer98]), p.14 (PDF p.15).

Z. Zou, *Pure Differentially Private Query Release via Laplace Input Smoothing*, arXiv:2611.04721
(held version, sha256 69b70d59…).

"For any coupling (X, Y) of finite laws P, Q, ‖P − Q‖_TV ≤ Pr{X ≠ Y}, and a coupling attaining
equality exists."

**Formalization Note.** Laws on the finite set `Y` are functions `Y → ℝ` (`IsPMF`); a coupling
is the joint law `μ` of `(X, Y)` on `Y × Y` with marginals `P` and `Q` (`IsCoupling`), and
`Pr{X ≠ Y} = ∑_{(x,y) : x ≠ y} μ(x, y)`. `‖P − Q‖_TV` is `tvDist P Q` (p.14). -/
theorem lemma_12 {Y : Type*} [Fintype Y] [DecidableEq Y] (P Q : Y → ℝ) (hP : IsPMF P)
    (hQ : IsPMF Q) :
    (∀ μ : Y × Y → ℝ, IsCoupling P Q μ →
        tvDist P Q ≤ ∑ z ∈ Finset.univ.filter (fun z : Y × Y => z.1 ≠ z.2), μ z) ∧
      ∃ μ : Y × Y → ℝ, IsCoupling P Q μ ∧
        tvDist P Q = ∑ z ∈ Finset.univ.filter (fun z : Y × Y => z.1 ≠ z.2), μ z := by sorry

end PureDPQR
