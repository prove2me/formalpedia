-- Prove2me | Theorems.Thm_RadGauss_LipschitzGaussian_theorem_14
-- name    : RadGauss.LipschitzGaussian.theorem_14
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T09:06:12.193562+00:00
-- url     : https://prove2.me/theorems/6a51fd00-7195-4332-9286-26d55749da16
-- title:
--   Theorem 14 — Ĝ_n(φ∘F) ≤ 2L Σ_i Ĝ_n(F_i) for an L-Lipschitz φ of a direct sum of classes
-- statement:
--   Let $\mathcal A = \mathbb R^m$ with the Euclidean distance, and let $F$ be a class of functions $\mathcal X \to \mathcal A$ that is a subset of the direct sum of real-valued classes $F_1, \dots, F_m$: every $f \in F$ is $x \mapsto (f_1(x), \dots, f_m(x))$ with $f_i \in F_i$. Let $\phi : \mathcal Y \times \mathcal A \to \mathbb R$ be such that
--
--   1. for every $y \in \mathcal Y$, $\phi(y, \cdot)$ is Lipschitz with constant $L \ge 0$ with respect to the Euclidean distance on $\mathcal A$;
--   2. $\phi(y, 0) = 0$ for every $y$ (it passes through the origin);
--   3. $\phi$ is uniformly bounded: $|\phi(y, a)| \le M$ for some $M$ and all $y, a$.
--
--   For $f \in F$ let $\phi \circ f$ be the map $(x, y) \mapsto \phi(y, f(x))$. Then for every integer $n$ and every sample $(x_1, y_1), \dots, (x_n, y_n)$,
--
--   $$
--   \hat G_n(\phi\circ F) \le 2L \sum_{i=1}^m \hat G_n(F_i),
--   $$
--
--   where the left side is the empirical Gaussian complexity of $\phi\circ F$ at the sample $((x_k, y_k))_{k\le n}$ and the right side uses the empirical Gaussian complexities of the $F_i$ at $(x_k)_{k \le n}$.
--
--   This is the vector-valued contraction principle for Gaussian averages: composing a direct sum of classes with a Lipschitz function costs at most the Lipschitz constant times the sum of the component complexities.
--
--   **Formalization Note** $\mathcal A$ is `EuclideanSpace ℝ (Fin m)` (not the sup-norm space `Fin m → ℝ`). $L$ is a nonnegative real. The empirical Gaussian complexities take values in $[0,\infty]$, so no finiteness or boundedness of the $F_i$ is assumed (the paper's "without loss of generality each $F_i$ is finite" is a proof step). The printed proof uses Lemma 13 and identifies $\mathbb E\sup_\alpha X_\alpha$ with $n\hat G_n(\phi\circ F)$, ignoring the absolute value and the factor $2$ of Definition 2; with Lemma 13's constant $2$ that argument yields only $4L$. The statement with $2L$ is nevertheless true: it follows from the constant-$1$ Sudakov–Fernique comparison (`HighDimProb.RandomProcesses.sudakov_fernique_finite_dim`) after adjoining a zero index and using the symmetry of the Gaussian vector. The constant $2L$ is kept as printed.
-- source:
--   Bartlett, Mendelson, Rademacher and Gaussian Complexities: Risk Bounds and Structural Results, J. Mach. Learn. Res. 3 (2002), p. 471 (PDF p. 9), Theorem 14

import Mathlib
import Definitions.Def_RadGauss_LipschitzGaussian_GaussianComplexity
import Definitions.Def_RadGauss_LipschitzGaussian_Classes

open MeasureTheory
open scoped ENNReal NNReal

namespace RadGauss.LipschitzGaussian

/-- **Theorem 14** (p. 471): for `A = ℝ^m` with the Euclidean distance, a class `F` of maps
`𝒳 → A` contained in the direct sum of real classes `F_1, …, F_m`, and `φ : 𝒴 × A → ℝ` such
that every `φ(y, ·)` is `L`-Lipschitz, vanishes at the origin and `φ` is uniformly bounded,
every sample `(x_1, y_1), …, (x_n, y_n)` satisfies
`Ĝ_n(φ ∘ F) ≤ 2L Σ_i Ĝ_n(F_i)`, the right side evaluated at `x_1, …, x_n`. -/
theorem theorem_14 {X Y : Type*} {m : ℕ} (F : Set (X → EuclideanSpace ℝ (Fin m)))
    (Fi : Fin m → Set (X → ℝ)) (hF : SubsetDirectSum F Fi)
    (φ : Y → EuclideanSpace ℝ (Fin m) → ℝ) (L : ℝ≥0)
    (hLip : ∀ y, LipschitzWith L (φ y)) (hzero : ∀ y, φ y 0 = 0)
    (hbdd : ∃ M : ℝ, ∀ y a, |φ y a| ≤ M)
    (n : ℕ) (s : Fin n → X × Y) :
    empiricalGaussian n (compClass φ F) s ≤
      2 * (L : ℝ≥0∞) * ∑ i, empiricalGaussian n (Fi i) (fun k => (s k).1) := by sorry

end RadGauss.LipschitzGaussian
