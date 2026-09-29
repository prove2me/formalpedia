-- Prove2me | Theorems.Thm_SPOBounds_Natarajan_rademacher_generalization_bound
-- name    : SPOBounds.Natarajan.rademacher_generalization_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-26T18:27:48.20999+00:00
-- url     : https://prove2.me/theorems/374973f0-2e19-484b-ab6f-77547f8646e7
-- title:
--   Theorem 1 — Rademacher generalization bound for the SPO loss
-- statement:
--   Let $S\subseteq\mathbb R^d$ be nonempty, compact and convex, let $w^*$ be any optimization oracle for $S$, and let $\mathcal C\subseteq\mathbb R^d$ be a nonempty bounded set. Let $\mathcal D$ be a probability distribution on $\mathcal X\times\mathbb R^d$ whose cost component lies in $\mathcal C$ almost surely, and let $\mathcal H$ be a family of functions $f:\mathcal X\to\mathbb R^d$. Then for every $n\ge1$ and every $\delta>0$, with probability at least $1-\delta$ over an i.i.d. sample $(x_1,c_1),\dots,(x_n,c_n)$ from $\mathcal D$, every $f\in\mathcal H$ satisfies
--   $$R_{\rm SPO}(f)\le\hat R_{\rm SPO}(f)+2\,\mathfrak R^n_{\rm SPO}(\mathcal H)+\omega_S(\mathcal C)\sqrt{\frac{\log(1/\delta)}{2n}}.$$
--
--   This is the Bartlett–Mendelson bound adapted to the SPO loss, whose values lie in $[0,\omega_S(\mathcal C)]$. It holds uniformly over $\mathcal H$, so it applies to any training procedure that returns a member of $\mathcal H$; the remaining work is to bound $\mathfrak R^n_{\rm SPO}(\mathcal H)$.
--
--   **Formalization Note** "With probability at least $1-\delta$" is stated as: the product measure $\mathcal D^n$ of the set of samples on which some $f\in\mathcal H$ violates the inequality is at most $\delta$ (measure of a possibly non-measurable set is its outer measure, so this is the strong form). The paper is silent on measurability; three hypotheses are added: each $z\mapsto\ell_{\rm SPO}(f(z_1),z_2)$, $f\in\mathcal H$, is measurable (so $R_{\rm SPO}(f)$ is a genuine expectation); the uniform deviation $\sup_{f\in\mathcal H}(R_{\rm SPO}(f)-\hat R_{\rm SPO}(f))$ is a.e.-measurable in the sample (the McDiarmid step); and for each sign vector $\sigma$ the supremum $\sup_{f\in\mathcal H}\frac1n\sum_i\sigma_i\ell_{\rm SPO}(f(x_i),c_i)$ is a.e.-measurable in the sample (the symmetrization step; it also makes $\mathfrak R^n_{\rm SPO}(\mathcal H)$ a genuine expectation rather than the default value $0$ of a non-integrable Bochner integral). The logarithm is natural. For $\delta\ge1$ the claim is trivial.
-- source:
--   El Balghiti, Elmachtoub, Grigas, Tewari, Generalization Bounds in the Predict-then-Optimize Framework, arXiv:1905.11488v3, p. 9, Theorem 1

import Mathlib
import Definitions.Def_SPOBounds_Natarajan_Model
import Definitions.Def_SPOBounds_Natarajan_Rademacher

open MeasureTheory

namespace SPOBounds.Natarajan

/-- **Theorem 1** (arXiv:1905.11488v3, p. 9). For a nonempty compact convex `S`, any oracle `w`,
cost vectors almost surely in the nonempty bounded set `C`, and any `δ > 0`: with probability at
least `1 − δ` over an i.i.d. sample of size `n`, every `f ∈ H` satisfies
`R_SPO(f) ≤ R̂_SPO(f) + 2 ℜⁿ_SPO(H) + ω_S(C) √(log(1/δ) / (2n))`.
Stated as: the (outer) `Dⁿ`-measure of the samples on which some `f ∈ H` violates the bound is
at most `δ`. The measurability hypotheses `hℓ`, `hΦ`, `hA` are added (the paper is silent). -/
theorem rademacher_generalization_bound {d : ℕ} {X : Type*} [MeasurableSpace X]
    (S : Set (EuclideanSpace ℝ (Fin d))) (hS : S.Nonempty) (hSc : IsCompact S)
    (hSv : Convex ℝ S)
    (w : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (hw : IsOracle S w)
    (C : Set (EuclideanSpace ℝ (Fin d))) (hC : C.Nonempty) (hCb : Bornology.IsBounded C)
    (D : Measure (X × EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure D]
    (hDC : ∀ᵐ z ∂D, z.2 ∈ C)
    (H : Set (X → EuclideanSpace ℝ (Fin d)))
    (hℓ : ∀ f ∈ H, Measurable (fun z : X × EuclideanSpace ℝ (Fin d) => spoLoss w (f z.1) z.2))
    (n : ℕ) (hn : 0 < n)
    (hΦ : AEMeasurable (fun s : Fin n → X × EuclideanSpace ℝ (Fin d) => supDeviation D w H s)
      (Measure.pi fun _ : Fin n => D))
    (hA : ∀ σ : Fin n → Bool,
      AEMeasurable (fun s : Fin n → X × EuclideanSpace ℝ (Fin d) => signedSup w H σ s)
        (Measure.pi fun _ : Fin n => D))
    (δ : ℝ) (hδ : 0 < δ) :
    Measure.pi (fun _ : Fin n => D)
        {s | ∃ f ∈ H, ¬ (spoRisk D w f ≤ empRisk w f s + 2 * expRademacherSPO D w H n +
          linGapSet S C * Real.sqrt (Real.log (1 / δ) / (2 * n)))} ≤ ENNReal.ofReal δ := by sorry

end SPOBounds.Natarajan
