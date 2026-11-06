-- Prove2me | Theorems.Thm_SymNormLoad_lemma_2_5
-- name    : SymNormLoad.lemma_2_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:32:51.45491+00:00
-- url     : https://prove2.me/theorems/1eb5c003-56de-4587-95a7-04d40e7c3a57
-- title:
--   Lemma 2.5 — convexity and relative growth of the transform
-- statement:
--   Let $M\ge2$, $\Psi$ a monotone symmetric norm on $\mathbb R^M$, and $h$ the load transform of (2.2). Then on $[0,\infty)$:
--
--   1. $h$ is (strictly) increasing;
--   2. $h$ is concave;
--   3. $t\mapsto\exp(h(t))$ is convex;
--   4. consequently, for every $b\ge0$, the increment $\exp(h(L+b))-\exp(h(L))$ is nondecreasing in $L\ge0$.
--
--   Clause 4 is the property the telescoping argument of Lemma 2.6 uses: a fixed load increment costs no less on a more loaded machine.
--
--   Differences from the source:
--   - reading: h is increasing → StrictMonoOn h (Set.Ici 0); reason: p.13 uses "Since h is strictly increasing"; the strict reading is the stronger one
--   - encoding: the clauses for t ≥ 0 / L ≥ 0 (domain of h) → StrictMonoOn, ConcaveOn, ConvexOn and MonotoneOn on Set.Ici 0; reason: h is defined on [0, ∞)
--   - encoding: the load transform h : [0, ∞) → [0, ∞) defined by (2.2) → any h : ℝ → ℝ with IsLoadTransform Ψ h (h 0 = 0 and the derivative of (2.2) within [0, ∞) at every t ≥ 0); reason: (2.2) has exactly one solution on [0, ∞) (milestone eq_2_2), and values on t < 0 are never used; same h
--   - encoding: a monotone symmetric norm Ψ : ℝ^M → ℝ≥0 with machines 1, …, M → a function Ψ : (Fin M → ℝ) → ℝ with IsMonotoneSymmetricNorm Ψ (norm axioms, permutation invariance, monotonicity on the orthant); machines 0, …, M−1; reason: Lean convention; the same norms, relabelled coordinates
-- source:
--   Chen–Im–Sirri, Online Load Balancing under Symmetric Norms, manuscript (STOC 2027 submission), Lemma 2.5, p.10 (proof App. A.1, p.38)

import Mathlib
import Definitions.Def_SymNormLoad_IsMonotoneSymmetricNorm
import Definitions.Def_SymNormLoad_IsLoadTransform

namespace SymNormLoad

/-- **Lemma 2.5 (convexity and relative growth).** Chen–Im–Sirri, *Online Load Balancing under
Symmetric Norms*, manuscript (STOC 2027 submission), Lemma 2.5, p.10 (proof in App. A.1, p.38).
The transform `h` is increasing and concave, while its exponential `t ↦ exp(h(t))` is convex.
Consequently, for any `b ≥ 0`, the increment `exp(h(L + b)) − exp(h(L))` is nondecreasing in
`L ≥ 0`.

**Formalization Note** All four clauses are on `[0, ∞)`, the domain of `h`. "Increasing" is read
as strictly increasing (p.13 uses "Since h is strictly increasing"). `2 ≤ M` is the standing
assumption of §1.1. -/
theorem lemma_2_5 (M : ℕ) (hM : 2 ≤ M) (Ψ : (Fin M → ℝ) → ℝ)
    (hΨ : IsMonotoneSymmetricNorm Ψ) (h : ℝ → ℝ) (hh : IsLoadTransform Ψ h) :
    StrictMonoOn h (Set.Ici 0) ∧ ConcaveOn ℝ (Set.Ici 0) h ∧
      ConvexOn ℝ (Set.Ici 0) (fun t => Real.exp (h t)) ∧
      ∀ b : ℝ, 0 ≤ b →
        MonotoneOn (fun L => Real.exp (h (L + b)) - Real.exp (h L)) (Set.Ici 0) := by sorry

end SymNormLoad
