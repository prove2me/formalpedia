-- Prove2me | Theorems.Thm_QuadPTFLearn_lemma_4_3
-- name    : QuadPTFLearn.lemma_4_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T03:27:00.783275+00:00
-- url     : https://prove2.me/theorems/1857567f-c4d9-4415-a2cf-bf1e60bdc618
-- title:
--   Lemma 4.3, p.29 — $\Pr_{z\sim N(0,I_U)}[\|p_z\|_2<\kappa\|p\|_2]\le K\sqrt\kappa$ for a nonzero quadratic $p$
-- statement:
--   There is a universal constant $K\ge1$ such that the following holds. Let $p:\mathbb R^d\to\mathbb R$ be a nonzero polynomial of degree at most two and $U\subseteq\mathbb R^d$ a subspace. For $z\in U$ let $p_z(x)=p(z+\mathrm{proj}_{U^\perp}x)$. Then for every $\kappa\in(0,1)$,
--   $$\Pr_{z\sim N(0,I_U)}\big[\|p_z\|_2<\kappa\|p\|_2\big]\le K\sqrt\kappa .$$
--
--   Fixing the coordinates of a quadratic in a random point of a subspace rarely makes it small.
--
--   Differences from the source:
--   - encoding: z ∼ N(0, I_U) → z = proj_U x with x ∼ N(0, I_d); reason: proj_U of a standard Gaussian has law N(0, I_U)
-- source:
--   Diakonikolas, Kane, Ma, Ren, Tran, Beyond Multi-Index Models: Learning Intersections of Degree-2 PTFs, arXiv:2611.05114 (sha256 4d6ea892…), Lemma 4.3, p.29 (PDF p.31)

import Mathlib
import Definitions.Def_QuadPTFLearn_Regularity

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace QuadPTFLearn

/-- I. Diakonikolas, D. M. Kane, M. Ma, L. Ren, T. Tran, *Beyond Multi-Index Models: Learning
Intersections of Degree-2 PTFs*, arXiv:2611.05114 (held copy, sha256 4d6ea892…5aed).
Lemma 4.3, p.29 (PDF p.31).

There is a universal constant `K ≥ 1` such that the following holds. Let `p : ℝᵈ → ℝ` be a
nonzero polynomial of degree at most two and `U ⊆ ℝᵈ` a subspace. For `z ∈ U` let
`p_z(x) = p(z + proj_{U⊥} x)`. Then for every `κ ∈ (0, 1)`,
`Pr_{z∼N(0,I_U)}[‖p_z‖₂ < κ ‖p‖₂] ≤ K √κ`.

**Formalization Note.** `z ∼ N(0, I_U)` is written as `z = proj_U x` with `x ∼ N(0, I_d)`, which
has that law. -/
theorem lemma_4_3 :
    ∃ K : ℝ, 1 ≤ K ∧
      ∀ (d : ℕ) (p : Poly d), p ≠ 0 → p.totalDegree ≤ 2 → ∀ U : Submodule ℝ (Pt d),
      ∀ κ : ℝ, 0 < κ → κ < 1 →
        gauss d {x | l2norm (fun y => peval p (projV U x + projV Uᗮ y)) <
            κ * l2norm (peval p)} ≤ ENNReal.ofReal (K * Real.sqrt κ) := by sorry

end QuadPTFLearn
