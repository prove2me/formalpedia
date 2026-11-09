-- Prove2me | Theorems.Thm_SharpConsist_lemma_B_1_b
-- name    : SharpConsist.lemma_B_1_b
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T12:12:48.19465+00:00
-- url     : https://prove2.me/theorems/f718be17-c9c0-4da7-b937-2f9a84de4af5
-- title:
--   Lemma B.1(b) — derivative bounds within each branch
-- statement:
--   Fix $T\in[7/5,3/2]$ and an integer $m\ge32$, let $P$ be either $F_\delta$ or $K_\delta$ of Eq. (5.5), regarded as a function of $p=(x,y)$, and let $R=[0,1]\times[0,m]$ and $s=x+y$. Then:
--
--   1. $P$ is $C^1$ with locally Lipschitz gradient on an open set containing $R$;
--   2. for $i\in\{x,y\}$ and $p\in R$, $$\frac{16e^{-s}}{m}\le\partial_iP(p)\le4;$$
--   3. for almost every $p\in R$ and all $i,j\in\{x,y\}$, the second partial $\partial_{ij}P(p)$ — the derivative at $\tau=0$ of $\tau\mapsto\partial_iP(p+\tau e_j)$ — exists and satisfies $\partial_{ij}P(p)\le-16e^{-s}/m$;
--   4. each first partial $\partial_iP$ is nonincreasing as either coordinate increases, along every coordinate segment in $R$ (including segments crossing or lying on piece boundaries).
--
--   These are the within-branch signs that certify monotonicity and diminishing returns of the discrete instance.
--
--   **Formalization Note.** Partials are `fderiv ℝ P p` applied to $(1,0)$ or $(0,1)$; "almost every" refers to Lebesgue measure on $\mathbb R^2$.
--
--   Differences from the source:
--   - reading: "Each profile P is C¹ with locally Lipschitz gradient" on the closed rectangle → C¹ with locally Lipschitz gradient on an open set U containing the rectangle; reason: the usual meaning of C¹ on a closed set; it makes the partials at boundary points two-sided derivatives (the stronger reading)
--   - reading: "∂_ij P ≤ −16e^{−s}/m almost everywhere" → for Lebesgue-a.e. p in the rectangle and all i, j, the derivative at 0 of τ ↦ ∂_iP(p + τ e_j) exists and is ≤ −16e^{−s}/m; reason: the gradient is only locally Lipschitz, so second partials exist only almost everywhere; existence is asserted, not assumed
--   - encoding: partial derivatives ∂_x, ∂_y of the profiles → fderiv ℝ of the profile on ℝ × ℝ applied to (1, 0) or (0, 1); reason: the profiles are C¹ near the rectangle (Lemma B.1(b)), so these are the genuine partials
--   - encoding: v, w defined on [0, ∞) → v, w defined on ℝ by the quadratic/linear piece for t ≤ T; reason: every argument the statement evaluates is nonnegative (t = ω_m y ≥ 0, z between t and s ≥ 0)
-- source:
--   Fu–Zhang–Tao, A Sharp Barrier of Consistent Submodular Maximization, arXiv:2609.09986 (held version, sha256 874ec76c…), Appendix B.2, Lemma B.1(b), p.34

import Mathlib
import Definitions.Def_SharpConsist_Fdelta

namespace SharpConsist

/-- **Lemma B.1(b) (within each branch).** Fu–Zhang–Tao, *A Sharp Barrier of Consistent Submodular Maximization*, arXiv:2609.09986 (held version, sha256 874ec76c…), Appendix B.2, Lemma B.1(b), p.34.
Fix `T ∈ [7/5, 3/2]` and an integer `m ≥ 32`, and let `P` be `F_δ` or `K_δ` of Eq. (5.5), viewed as
a function of `p = (x, y)`, on the rectangle `R = [0, 1] × [0, m]`, with `s = x + y`.
1. `P` is `C¹` with locally Lipschitz gradient (on an open set containing `R`).
2. For `i ∈ {x, y}` and `p ∈ R`: `16e^{−s}/m ≤ ∂_i P(p) ≤ 4`.
3. For almost every `p ∈ R` and `i, j ∈ {x, y}`: the second partial `∂_{ij}P(p)` (the derivative at
   `τ = 0` of `τ ↦ ∂_i P(p + τ e_j)`) exists and is at most `−16e^{−s}/m`.
4. Each first partial `∂_i P` is nonincreasing as either coordinate increases, along every coordinate
   segment in `R`.

**Formalization Note.** Partial derivatives are `fderiv ℝ P p e` with `e = (1, 0)` or `(0, 1)`; clause 1
makes them genuine derivatives on `R`. "Almost everywhere" is with respect to Lebesgue measure on
`ℝ × ℝ`; the second partial is asserted to exist at almost every point (the gradient is only locally
Lipschitz). -/
theorem lemma_B_1_b (T : ℝ) (hT : T ∈ Set.Icc (7 / 5 : ℝ) (3 / 2)) (m : ℕ) (hm : 32 ≤ m) :
    ∀ P : ℝ × ℝ → ℝ, (P = fun p => Fdelta T m p.1 p.2) ∨ (P = fun p => Kdelta T m p.1 p.2) →
      (∃ U : Set (ℝ × ℝ), IsOpen U ∧ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) m ⊆ U ∧
        ContDiffOn ℝ 1 P U ∧ LocallyLipschitzOn U (fderiv ℝ P)) ∧
      (∀ p ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) m, ∀ e ∈ ({(1, 0), (0, 1)} : Set (ℝ × ℝ)),
        16 * Real.exp (-(p.1 + p.2)) / (m : ℝ) ≤ fderiv ℝ P p e ∧ fderiv ℝ P p e ≤ 4) ∧
      (∀ᵐ p ∂(MeasureTheory.volume : MeasureTheory.Measure (ℝ × ℝ)),
        p ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) m →
        ∀ e ∈ ({(1, 0), (0, 1)} : Set (ℝ × ℝ)), ∀ e' ∈ ({(1, 0), (0, 1)} : Set (ℝ × ℝ)),
          ∃ H : ℝ, HasDerivAt (fun τ : ℝ => fderiv ℝ P (p + τ • e') e) H 0 ∧
            H ≤ -(16 * Real.exp (-(p.1 + p.2)) / (m : ℝ))) ∧
      (∀ p ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) m, ∀ e ∈ ({(1, 0), (0, 1)} : Set (ℝ × ℝ)),
        ∀ e' ∈ ({(1, 0), (0, 1)} : Set (ℝ × ℝ)), ∀ τ : ℝ, 0 ≤ τ →
          p + τ • e' ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) m →
          fderiv ℝ P (p + τ • e') e ≤ fderiv ℝ P p e) := by sorry

end SharpConsist
