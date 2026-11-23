-- Prove2me | Theorems.Thm_SPOBounds_Natarajan_Supplement_margin_generalization_bound_uniform
-- name    : SPOBounds.Natarajan.Supplement.margin_generalization_bound_uniform
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T04:39:21.022804+00:00
-- url     : https://prove2.me/theorems/569a9dae-f484-4328-a284-ae9d15939245
-- title:
--   Theorem 5 — margin-based SPO generalization bound uniform over $\gamma\in(0,\bar\gamma]$
-- statement:
--   Work in the $\ell_2$ set-up: decisions lie in the Euclidean space $\mathbb R^d$, and the feasible region $S$ is nonempty, compact, convex and not a singleton. Let $w^*$ be any optimization oracle, and suppose $S$ satisfies the strength property with parameter $\mu>0$ with respect to the $\ell_2$-norm. Let $\mathcal D$ be a distribution of (feature, cost) pairs $(x,c)$ whose cost lies almost surely in a nonempty bounded set $\mathcal C$, with $\rho_2(\mathcal C)=\sup_{c\in\mathcal C}\|c\|_2$ and $\omega_S(\mathcal C)=\sup_{c\in\mathcal C}\omega_S(c)$. Let $\mathcal H$ be a family of prediction functions from features to $\mathbb R^d$, $\mathfrak R^n(\mathcal H)$ its expected multivariate Rademacher complexity, and $\hat R^\gamma_{\rm SPO}(f)$ the empirical $\gamma$-margin SPO risk on a sample of size $n\ge1$. Fix $\bar\gamma>0$.
--
--   Then for any $\delta>0$, with probability at least $1-\delta$ over an i.i.d. sample from $\mathcal D$, the following holds **simultaneously for all** $f\in\mathcal H$ and **all** $\gamma\in(0,\bar\gamma]$:
--   $$R_{\rm SPO}(f)\le\hat R^\gamma_{\rm SPO}(f)+\left(\frac{4\sqrt2\,\rho_2(\mathcal C)+4\sqrt2\,\mu\,\omega_S(\mathcal C)}{\gamma\mu}\right)\mathfrak R^n(\mathcal H)+\omega_S(\mathcal C)\left(\sqrt{\frac{\log(\log_2(2\bar\gamma/\gamma))}{n}}+\sqrt{\frac{\log(2/\delta)}{2n}}\right).$$
--
--   Compared with Theorem 4, which holds for one fixed margin $\gamma$, this bound allows $\gamma$ to be chosen after seeing the data, for instance by cross-validation, at the price of doubled constants, $\log(2/\delta)$ in place of $\log(1/\delta)$, and a $\log\log$ term.
--
--   **Formalization Note** The statement says that the outer $\mathcal D^n$-measure of the set of samples on which some $f\in\mathcal H$ and some $\gamma\in(0,\bar\gamma]$ violate the bound is at most $\delta$; one failure event covers all $f$ and all $\gamma$. Costs are continuous linear functionals on $\mathbb R^d$ with the Borel σ-algebra. $\log$ is the natural logarithm and $\log_2$ is `Real.logb 2`; on $(0,\bar\gamma]$ one has $\log_2(2\bar\gamma/\gamma)\ge1$, so the outer logarithm is nonnegative. The side conditions are those of the published Theorem 4 (`SPOBounds.Margin.margin_generalization_bound`), required at every $\gamma\in(0,\bar\gamma]$: measurability of each $f\in\mathcal H$ and of its SPO loss, almost-everywhere measurability of the uniform deviation and of the margin Rademacher suprema, almost-sure boundedness of the multivariate Rademacher suprema, and integrability of the empirical multivariate Rademacher complexity.
--
--   Differences from the source:
--
--   - encoding: cost vectors in ℝ^d; 'with probability at least 1 − δ' → continuous linear functionals on Euclidean ℝ^d; outer Dⁿ-measure of the failure event ≤ δ; reason: Riesz identification; the outer-measure form equals the probability statement for measurable events
--   - reading: risks and Rademacher complexities are expectations assumed to exist → measurability, a.s. boundedness and integrability side conditions of the published Theorem 4, for every γ ∈ (0, γ̄]; reason: the source is silent on measurability; without them the Lean integrals and suprema take junk values
--   - generalization: feature domain 𝒳 ⊆ ℝ^p → an arbitrary measurable feature type X; reason: The bound uses features only through evaluations f(x) and the sample law; taking X to be the source feature domain recovers every source instance with all constants unchanged.
-- source:
--   El Balghiti, Elmachtoub, Grigas, Tewari, Generalization Bounds in the Predict-then-Optimize Framework, arXiv:1905.11488v3, p. 20, Theorem 5 (proof in Appendix C.1, p. 33)

import Mathlib
import Definitions.Def_SPOBounds_Margin_Model
import Definitions.Def_SPOBounds_Margin_Degeneracy
import Definitions.Def_SPOBounds_Margin_Rademacher

open MeasureTheory SPOBounds.Margin

namespace SPOBounds.Natarajan.Supplement

/-- **Theorem 5** (arXiv:1905.11488v3, p. 20). ℓ₂ set-up of Theorem 4: `E = ℝ^d` Euclidean, costs
and predictions in its dual with the Borel σ-algebra. Let `S` be nonempty, compact, convex and not
a singleton, `w` any oracle, and suppose `S` has the strength property with parameter `μ > 0`.
Fix `γ̄ > 0`, a nonempty bounded `C` containing the cost a.s., and `δ > 0`. Then with probability
at least `1 − δ` over an i.i.d. sample of size `n`, **every** `f ∈ H` and **every**
`γ ∈ (0, γ̄]` satisfy
`R_SPO(f) ≤ R̂^γ_SPO(f) + ((4√2 ρ₂(C) + 4√2 μ ω_S(C)) / (γ μ)) ℜⁿ(H)
  + ω_S(C) (√(log(log₂(2γ̄/γ)) / n) + √(log(2/δ) / (2n)))`.
Stated as: the (outer) `Dⁿ`-measure of the samples on which some `f ∈ H` and some `γ ∈ (0, γ̄]`
violate the bound is at most `δ`. The measurability, boundedness and integrability side conditions
are those of the published Theorem 4 (`SPOBounds.Margin.margin_generalization_bound`), required
at every `γ ∈ (0, γ̄]`. -/
theorem margin_generalization_bound_uniform {d : ℕ} {X : Type*} [MeasurableSpace X]
    [MeasurableSpace (StrongDual ℝ (EuclideanSpace ℝ (Fin d)))]
    [BorelSpace (StrongDual ℝ (EuclideanSpace ℝ (Fin d)))]
    (S : Set (EuclideanSpace ℝ (Fin d))) (hS : S.Nonempty) (hSc : IsCompact S)
    (hSv : Convex ℝ S) (hSnt : S.Nontrivial)
    (w : StrongDual ℝ (EuclideanSpace ℝ (Fin d)) → EuclideanSpace ℝ (Fin d)) (hw : IsOracle S w)
    (μ : ℝ) (hμ : 0 < μ) (hstr : StrengthProperty S μ w)
    (γbar : ℝ) (hγbar : 0 < γbar)
    (C : Set (StrongDual ℝ (EuclideanSpace ℝ (Fin d)))) (hC : C.Nonempty)
    (hCb : Bornology.IsBounded C)
    (D : Measure (X × StrongDual ℝ (EuclideanSpace ℝ (Fin d)))) [IsProbabilityMeasure D]
    (hDC : ∀ᵐ z ∂D, z.2 ∈ C)
    (H : Set (X → StrongDual ℝ (EuclideanSpace ℝ (Fin d))))
    (hf : ∀ f ∈ H, Measurable f)
    (hℓ : ∀ f ∈ H,
      Measurable (fun z : X × StrongDual ℝ (EuclideanSpace ℝ (Fin d)) => spoLoss w (f z.1) z.2))
    (n : ℕ) (hn : 0 < n)
    (hΦ : ∀ γ ∈ Set.Ioc (0 : ℝ) γbar, AEMeasurable
      (fun s : Fin n → X × StrongDual ℝ (EuclideanSpace ℝ (Fin d)) =>
        marginSupDeviation S w γ D H s)
      (Measure.pi fun _ : Fin n => D))
    (hA : ∀ γ ∈ Set.Ioc (0 : ℝ) γbar, ∀ σ : Fin n → Bool,
      AEMeasurable
        (fun s : Fin n → X × StrongDual ℝ (EuclideanSpace ℝ (Fin d)) =>
          marginSignedSup S w γ H σ s)
        (Measure.pi fun _ : Fin n => D))
    (hBdd : ∀ᵐ s ∂(Measure.pi fun _ : Fin n => D), ∀ σ : Fin n → Fin d → Bool,
      BddAbove (Set.range fun f : H => (1 / n : ℝ) *
        ∑ i, (f : X → StrongDual ℝ (EuclideanSpace ℝ (Fin d))) (s i).1 (signVec (σ i))))
    (hInt : Integrable
      (fun s : Fin n → X × StrongDual ℝ (EuclideanSpace ℝ (Fin d)) =>
        empRademacherMulti H (fun i => (s i).1))
      (Measure.pi fun _ : Fin n => D))
    (δ : ℝ) (hδ : 0 < δ) :
    Measure.pi (fun _ : Fin n => D)
        {s | ∃ f ∈ H, ∃ γ ∈ Set.Ioc (0 : ℝ) γbar, ¬ (spoRisk D w f ≤ empMarginRisk S w γ f s +
          (4 * Real.sqrt 2 * rhoSet C + 4 * Real.sqrt 2 * μ * omegaSet S C) / (γ * μ) *
            expRademacherMulti D H n +
          omegaSet S C * (Real.sqrt (Real.log (Real.logb 2 (2 * γbar / γ)) / n) +
            Real.sqrt (Real.log (2 / δ) / (2 * n))))} ≤ ENNReal.ofReal δ := by sorry

end SPOBounds.Natarajan.Supplement
