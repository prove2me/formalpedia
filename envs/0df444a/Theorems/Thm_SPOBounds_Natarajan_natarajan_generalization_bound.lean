-- Prove2me | Theorems.Thm_SPOBounds_Natarajan_natarajan_generalization_bound
-- name    : SPOBounds.Natarajan.natarajan_generalization_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T18:30:30.954443+00:00
-- url     : https://prove2.me/theorems/0d0183c1-3817-4431-b0a5-0f446bcee82a
-- title:
--   Theorem 2 — Natarajan-dimension generalization bound for the SPO loss over a polyhedron
-- statement:
--   Let $S\subseteq\mathbb R^d$ be a nonempty, compact, convex polyhedron and $\mathfrak S$ the set of its extreme points, and let $w^*$ be an optimization oracle for $S$ whose values are extreme points of $S$. Let $\mathcal C$ be a nonempty bounded set of cost vectors, let $\mathcal D$ be a probability distribution on $\mathcal X\times\mathbb R^d$ whose cost component lies in $\mathcal C$ almost surely, and let $\mathcal H$ be a family of functions $f:\mathcal X\to\mathbb R^d$. Let $k$ be a natural number such that every finite set N-shattered by $w^*(\mathcal H)=\{x\mapsto w^*(f(x)):f\in\mathcal H\}$ has at most $k$ points. Then for every $n\ge1$ and every $\delta>0$, with probability at least $1-\delta$ over an i.i.d. sample $(x_1,c_1),\dots,(x_n,c_n)$ drawn from $\mathcal D$, every $f\in\mathcal H$ satisfies
--   $$R_{\rm SPO}(f)\le\hat R_{\rm SPO}(f)+2\,\omega_S(\mathcal C)\sqrt{\frac{2k\log(n|\mathfrak S|^2)}{n}}+\omega_S(\mathcal C)\sqrt{\frac{\log(1/\delta)}{2n}}.$$
--
--   With $k=d_N(w^*(\mathcal H))$ this is the paper's Theorem 2: the SPO risk of every predictor in the class is controlled by its empirical SPO risk plus a term of order $\omega_S(\mathcal C)\sqrt{d_N\log(n|\mathfrak S|)/n}$, uniformly over the class and hence for any training procedure.
--
--   **Formalization Note** "With probability at least $1-\delta$" is stated as: the product measure $\mathcal D^n$ of the set of samples on which some $f\in\mathcal H$ violates the inequality is at most $\delta$ (outer measure for a non-measurable set, so the strong form). Added hypotheses, all disclosed: (i) the oracle returns extreme points of $S$, the proof's own "w.l.o.g." (p. 31), since p. 10 allows non-extreme optimal points under ties; (ii) the three measurability hypotheses of Theorem 1 (each loss function $z\mapsto\ell_{\rm SPO}(f(z_1),z_2)$ measurable; the uniform deviation and, for each sign vector, the signed supremum a.e.-measurable in the sample), on which the paper is silent. $d_N$ is replaced by an upper bound $k$ on the sizes of N-shattered sets (equivalent when $d_N<\infty$; the printed bound is vacuous otherwise). $|\mathfrak S|$ is `Set.ncard` of the extreme points; the logarithm is natural.
-- source:
--   El Balghiti, Elmachtoub, Grigas, Tewari, Generalization Bounds in the Predict-then-Optimize Framework, arXiv:1905.11488v3, p. 11, Theorem 2, second display

import Mathlib
import Definitions.Def_SPOBounds_Natarajan_Model
import Definitions.Def_SPOBounds_Natarajan_Rademacher
import Definitions.Def_SPOBounds_Natarajan_NatarajanDim

open MeasureTheory

namespace SPOBounds.Natarajan

/-- **Theorem 2, second display** (arXiv:1905.11488v3, p. 11). Let `S` be a nonempty compact
convex polyhedron with extreme-point set `𝔖`, let the oracle `w` return extreme points of `S`,
let every set N-shattered by `w*(H)` have at most `k` elements, and let the cost vectors lie
almost surely in the nonempty bounded set `C`. For any `δ > 0`, with probability at least
`1 − δ` over an i.i.d. sample of size `n ≥ 1`, every `f ∈ H` satisfies
`R_SPO(f) ≤ R̂_SPO(f) + 2 ω_S(C) √(2 k log(n |𝔖|²) / n) + ω_S(C) √(log(1/δ) / (2n))`.
Stated as: the (outer) `Dⁿ`-measure of the samples on which some `f ∈ H` violates the bound is
at most `δ`. The measurability hypotheses `hℓ`, `hΦ`, `hA` are added (the paper is silent). -/
theorem natarajan_generalization_bound {d : ℕ} {X : Type*} [MeasurableSpace X]
    (S : Set (EuclideanSpace ℝ (Fin d))) (hS : S.Nonempty) (hSc : IsCompact S)
    (hSv : Convex ℝ S) (hSp : IsPolyhedron S)
    (w : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (hw : IsOracle S w)
    (hwv : ∀ c, w c ∈ Set.extremePoints ℝ S)
    (C : Set (EuclideanSpace ℝ (Fin d))) (hC : C.Nonempty) (hCb : Bornology.IsBounded C)
    (D : Measure (X × EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure D]
    (hDC : ∀ᵐ z ∂D, z.2 ∈ C)
    (H : Set (X → EuclideanSpace ℝ (Fin d)))
    (hℓ : ∀ f ∈ H, Measurable (fun z : X × EuclideanSpace ℝ (Fin d) => spoLoss w (f z.1) z.2))
    (k : ℕ) (hk : ∀ T : Finset X, NShatters (oracleClass w H) T → T.card ≤ k)
    (n : ℕ) (hn : 0 < n)
    (hΦ : AEMeasurable (fun s : Fin n → X × EuclideanSpace ℝ (Fin d) => supDeviation D w H s)
      (Measure.pi fun _ : Fin n => D))
    (hA : ∀ σ : Fin n → Bool,
      AEMeasurable (fun s : Fin n → X × EuclideanSpace ℝ (Fin d) => signedSup w H σ s)
        (Measure.pi fun _ : Fin n => D))
    (δ : ℝ) (hδ : 0 < δ) :
    Measure.pi (fun _ : Fin n => D)
        {s | ∃ f ∈ H, ¬ (spoRisk D w f ≤ empRisk w f s +
          2 * linGapSet S C * Real.sqrt (2 * k *
            Real.log ((n : ℝ) * ((Set.extremePoints ℝ S).ncard : ℝ) ^ 2) / n) +
          linGapSet S C * Real.sqrt (Real.log (1 / δ) / (2 * n)))} ≤ ENNReal.ofReal δ := by sorry

end SPOBounds.Natarajan
