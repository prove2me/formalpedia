-- Prove2me | Theorems.Thm_TaoBR_linearizedRestriction_le_of_oscillatoryOp_le
-- name    : TaoBR.linearizedRestriction_le_of_oscillatoryOp_le
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-29T17:16:34.163623+00:00
-- url     : https://prove2.me/theorems/22f47167-3c3b-488f-a090-5a5e6781ab8b
-- title:
--   Theorem 4.9 — oscillatory integral bounds O(R^{−m/p′+ε}) imply Lᵠ bounds for the linearized restriction operators, q < p
-- statement:
--   Let $m - 1 \le n \le m$, let $\varphi : \mathbf R^n \times \mathbf R^m \to \mathbf R$ be smooth, and let $\psi : \mathbf R^n \times \mathbf R^m \to \mathbf C$ be smooth and compactly supported. Suppose the mixed Hessian $\partial^2\varphi/\partial x\,\partial y$ has rank $m - 1$ at every point of the support of $\psi$. Let $1 \le p \le \infty$. Suppose that for every $\varepsilon > 0$ there is $C$ such that the operators
--   $$S_R f(x) = \int e^{-2\pi i R\varphi(x, y)}\psi(x, y) f(y)\,dy$$
--   satisfy $\|S_R\|_{L^p(\mathbf R^m) \to L^p(\mathbf R^n)} \le C R^{-m/p' + \varepsilon}$ for all $R \ge 1$. Then for every $y_0 \in \mathbf R^m$ and every $1 \le q < p$ there is $C$ with
--   $$\|\Re_{y_0} f\|_{L^q(\mathbf R^n)} \le C\|f\|_{L^q(\mathbf R^m)}, \qquad \Re_{y_0} f(x) = \psi(x, y_0)\hat f(\nabla_y\varphi(x, y_0)),$$
--   for all Schwartz $f$ on $\mathbf R^m$.
--
--   *Formalization note.* The paper's "phase function of constant rank $m - 1$ in the sense of Hörmander [15]" is read as the rank condition on the mixed Hessian over the support of the amplitude, Hörmander's condition (3.1) ([Ark. Mat. 11 (1973) 1–11](https://doi.org/10.1007/BF02388505), §3). Hörmander's curvature condition (3.2) is not assumed: p. 10 notes that "the hypothesis of Theorem 4.2 implies that the restriction surface $\{\nabla_y\phi(x, y_0) : x \in \mathbf R^n\}$ cannot degenerate to infinite order because of the Knapp counterexample" ("Theorem 4.2" there is Theorem 4.9). The paper's condition $m - 1 \le n \le m$ is on natural numbers, where $m - 1$ is truncated at $0$.
-- source:
--   Tao, T., The Bochner–Riesz conjecture implies the restriction conjecture, Duke Math. J. 96 (1999) 363–375, https://doi.org/10.1215/S0012-7094-99-09610-2 (the author's preprint, https://www.math.ucla.edu/~tao/preprints/restriction.dvi, whose page numbers are used), p. 10, Theorem 4.9

import Mathlib
import Definitions.Def_TaoBR

open MeasureTheory
open scoped ENNReal NNReal SchwartzMap

namespace TaoBR

theorem linearizedRestriction_le_of_oscillatoryOp_le (n m : ℕ) (hnm : m - 1 ≤ n) (hmn : n ≤ m)
    (φ : E n → E m → ℝ) (ψ : E n → E m → ℂ) (hφ : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry φ))
    (hψ : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry ψ)) (hψc : HasCompactSupport (Function.uncurry ψ))
    (hrank : HasConstantRank φ ψ (m - 1)) (p : ℝ≥0∞) (hp : 1 ≤ p)
    (hS : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ R : ℝ, 1 ≤ R →
      opNorm p p (oscillatoryOp φ ψ R) ≤
        ENNReal.ofReal (C * R ^ (-((m : ℝ) * (conjExp p)⁻¹.toReal) + ε))) :
    ∀ y₀ : E m, ∀ q : ℝ≥0∞, 1 ≤ q → q < p → ∃ C : ℝ≥0, ∀ f : 𝓢(E m, ℂ),
      eLpNorm (linearizedRestriction φ ψ y₀ f) q volume ≤ C * eLpNorm f q volume := by
  sorry

end TaoBR
