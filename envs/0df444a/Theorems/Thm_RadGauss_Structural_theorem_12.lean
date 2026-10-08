-- Prove2me | Theorems.Thm_RadGauss_Structural_theorem_12
-- name    : RadGauss.Structural.theorem_12
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T15:50:00.205042+00:00
-- url     : https://prove2.me/theorems/8d6abf79-54a4-4c07-b039-1ddcd6e4d67c
-- title:
--   Theorem 12, parts 1–4 and 7 — structural properties of the Rademacher complexity R_n
-- statement:
--   **Theorem 12, parts 1–4 and 7 (Bartlett–Mendelson 2002, p. 469).** Let $\mu$ be a probability measure on a measurable space $\mathcal X$, $n\ge0$ an integer, and $R_n$ the Rademacher complexity of Definition 2 for an i.i.d. sample of size $n$ from $\mu$. For classes $F$, $F_1,\dots,F_k$ and $H$ of real functions on $\mathcal X$ write $\mathrm{conv}\,F$ for the convex combinations of functions from $F$, $-F=\{-f:f\in F\}$, $\mathrm{absconv}\,F=\mathrm{conv}(F\cup -F)$, $cF=\{cf:f\in F\}$, $\phi\circ F=\{\phi\circ f: f\in F\}$ and $\sum_{i=1}^kF_i=\{f_1+\dots+f_k: f_i\in F_i\}$. Then:
--
--   - **Part 1.** If $F\subseteq H$, then $R_n(F)\le R_n(H)$.
--   - **Part 2.** $R_n(F)=R_n(\mathrm{conv}\,F)=R_n(\mathrm{absconv}\,F)$.
--   - **Part 3.** For every $c\in\mathbb R$, $R_n(cF)=|c|\,R_n(F)$.
--   - **Part 4.** If $\phi:\mathbb R\to\mathbb R$ is Lipschitz with constant $L_\phi$ and $\phi(0)=0$, then $$R_n(\phi\circ F)\le 2L_\phi\,R_n(F).$$
--   - **Part 7.** $$R_n\Big(\sum_{i=1}^kF_i\Big)\le\sum_{i=1}^kR_n(F_i).$$
--
--   These are the "simple structural results" of the paper's Section 3.1: they bound the Rademacher complexity of a class built from simpler classes (by convex combination, scaling, composition with a Lipschitz map, or summation) in terms of the complexities of the pieces, which is how the paper obtains complexity bounds for voting methods, neural networks and loss classes.
--
--   **Formalization Note** The statement is the conjunction of the five parts, each universally quantified over its own classes. Parts 5 and 6 of the printed theorem are not included: part 5 ($R_n(F+h)\le R_n(F)+\|h\|_\infty/\sqrt n$) is false as printed, since its proof drops the factor $2/n$ of Definition 2 and the correct bound is $R_n(F)+2\|h\|_\infty/\sqrt n$ (for $F=\{0\}$, $h\equiv1$, $n=1$ the left side is $2$ and the printed right side is $1$), and part 6 is derived from part 5. Complexities are $[0,\infty]$-valued, so no class is assumed bounded. The convex hull is the set of finite convex combinations. The subadditivity conjunct carries one added hypothesis: each empirical complexity $x\mapsto\hat R_n(F_i)(x)$ is almost-everywhere measurable for $\mu^{\otimes n}$, so that the lower integral defining $R_n$ is additive.
-- source:
--   Bartlett, Mendelson, Rademacher and Gaussian Complexities: Risk Bounds and Structural Results, J. Mach. Learn. Res. 3 (2002), p. 469 (PDF p. 7), Theorem 12, parts 1–4 and 7

import Mathlib
import Definitions.Def_RadGauss_RiskBound_rademacherComplexity

open MeasureTheory
open scoped ENNReal Pointwise

namespace RadGauss.Structural

/-- **Theorem 12, parts 1–4 and 7** (Bartlett–Mendelson, JMLR 3 (2002), p. 469). Let `F`,
`F_1, …, F_k` and `H` be classes of real functions on `X` and `R_n` the Rademacher complexity
(Definition 2) for an i.i.d. sample from the probability measure `μ`. Then
1. if `F ⊆ H`, `R_n(F) ≤ R_n(H)`;
2. `R_n(F) = R_n(conv F) = R_n(absconv F)`;
3. for every `c ∈ ℝ`, `R_n(cF) = |c| R_n(F)`;
4. if `φ : ℝ → ℝ` is `L_φ`-Lipschitz with `φ(0) = 0`, `R_n(φ ∘ F) ≤ 2 L_φ R_n(F)`;
7. `R_n(Σ_{i=1}^k F_i) ≤ Σ_{i=1}^k R_n(F_i)` (each `R̂_n(F_i)` a.e.-measurable in the sample).
Parts 5 and 6 of the theorem are not included (part 5 is false as printed, part 6 rests on it). -/
theorem theorem_12 {X : Type*} [MeasurableSpace X] (μ : Measure X)
    [IsProbabilityMeasure μ] (n : ℕ) :
    (∀ F H : Set (X → ℝ), F ⊆ H → RadGauss.RiskBound.rademacherComplexity μ n F ≤ RadGauss.RiskBound.rademacherComplexity μ n H) ∧
    (∀ F : Set (X → ℝ),
      RadGauss.RiskBound.rademacherComplexity μ n F = RadGauss.RiskBound.rademacherComplexity μ n (convexHull ℝ F) ∧
        RadGauss.RiskBound.rademacherComplexity μ n (convexHull ℝ F) =
          RadGauss.RiskBound.rademacherComplexity μ n (convexHull ℝ (F ∪ -F))) ∧
    (∀ (F : Set (X → ℝ)) (c : ℝ),
      RadGauss.RiskBound.rademacherComplexity μ n (c • F) = ENNReal.ofReal |c| * RadGauss.RiskBound.rademacherComplexity μ n F) ∧
    (∀ (F : Set (X → ℝ)) (φ : ℝ → ℝ) (Lφ : NNReal), LipschitzWith Lφ φ → φ 0 = 0 →
      RadGauss.RiskBound.rademacherComplexity μ n ((fun f => φ ∘ f) '' F) ≤
        2 * (Lφ : ℝ≥0∞) * RadGauss.RiskBound.rademacherComplexity μ n F) ∧
    (∀ (k : ℕ) (Fs : Fin k → Set (X → ℝ)),
      (∀ i, AEMeasurable (RadGauss.RiskBound.empiricalRademacher n (Fs i)) (Measure.pi fun _ : Fin n => μ)) →
      RadGauss.RiskBound.rademacherComplexity μ n (∑ i, Fs i) ≤ ∑ i, RadGauss.RiskBound.rademacherComplexity μ n (Fs i)) := by sorry

end RadGauss.Structural
