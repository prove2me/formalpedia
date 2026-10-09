-- Prove2me | Theorems.Thm_RFRidge_Basic_lemma_2
-- name    : RFRidge.Basic.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T00:50:06.284683+00:00
-- url     : https://prove2.me/theorems/da5982a3-ee84-4d73-9bed-efe26364dcc8
-- title:
--   Lemma 2, p. 20 — a.s. in the features, S_M Ĉ_{M,λ}^{-1} S_M^*(I − P)f_ρ = 0 and ⟨f, (I − P)f_ρ⟩ = 0 for every f ∈ range(S_M)
-- statement:
--   Let $\psi,\pi,\kappa$ satisfy Assumption 3, let $\rho$ be a probability measure on $X\times\mathbb R$ with integrable $y$, and $\rho_X$ its marginal on $X$. Let $L$ be the integral operator of the kernel (6) on $L^2(X,\rho_X)$, let $P$ be the orthogonal projection onto the closure of the range of $L$, and let $f_\rho\in L^2(X,\rho_X)$ be the regression function $f_\rho(x)=\int y\,d\rho(y\mid x)$. Fix $M\in\mathbb N$. Then, for almost every draw of features $\omega_1,\dots,\omega_M$ i.i.d. from $\pi$:
--
--   1. for every $n$, every data set and every $\lambda>0$,
--   $$\big\|S_M\widehat C_{M,\lambda}^{-1}S_M^*(I-P)f_\rho\big\|_{\rho_X}=0;$$
--   2. for every $n$, every data set and every $\lambda>0$, $\langle\widehat f_{\lambda,M},(I-P)f_\rho\rangle_{\rho_X}=0$;
--   3. more generally, $\langle f,(I-P)f_\rho\rangle_{\rho_X}=0$ for every $f=\phi_M(\cdot)^\top\beta$ in the range of $S_M$.
--
--   Here $\widehat C_{M,\lambda}=\widehat C_M+\lambda I$, $S_M\beta=\phi_M(\cdot)^\top\beta$ and $(S_M^*g)_j=M^{-1/2}\int\psi(x,\omega_j)g(x)\,d\rho_X(x)$. The lemma removes the second term (18) of the excess-risk decomposition and the cross term of (16).
--
--   **Formalization Note** "a. s." is over the features: the data enter only through $\widehat C_M$ and the coefficients, and the statement holds for all data simultaneously. $(I-P)f_\rho$ is computed as the orthogonal projection of $f_\rho$ onto $(\operatorname{range}L)^\perp$, which is the orthogonal complement of the closure of the range. $L$ is any bounded operator on $L^2(X,\rho_X)$ that agrees almost everywhere with the integral operator; $f_\rho$ is characterized by $\int_{A\times\mathbb R}y\,d\rho=\int_A f_\rho\,d\rho_X$ for measurable $A$ and is assumed square integrable (Remark 6 gives this when $\int y^2d\rho<\infty$). The norm in item 1 is written as $\int(\cdot)^2\,d\rho_X=0$.
-- source:
--   Rudi & Rosasco, arXiv:1602.04474v5, Lemma 2, p. 20; Definition 1 and Definition 2, p. 18

import Mathlib
import Definitions.Def_RFRidge_Basic_Model

namespace RFRidge.Basic

open MeasureTheory Matrix

/-- Lemma 2, p. 20. Let `ρ_X = ρ.fst`, let `L` be the integral operator of the kernel (6) on
`L²(X, ρ_X)`, `P` the orthogonal projection onto the closure of its range, and `f_ρ` the regression
function (Definition 1, p. 18). Then for `π^{⊗M}`-almost every feature draw `ω`:
(1) `‖S_M Ĉ_{M,λ}^{-1} S_M^* (I − P) f_ρ‖_{ρ_X} = 0` for all data and all `λ > 0`;
(2) `⟨f̂_{λ,M}, (I − P) f_ρ⟩_{ρ_X} = 0` for all data and all `λ > 0`;
(3) more generally `⟨f, (I − P) f_ρ⟩_{ρ_X} = 0` for every `f = φ_M(·)^⊤ β ∈ range(S_M)`. -/
theorem lemma_2 {X W : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace W] [MeasurableSpace W] [BorelSpace W]
    (π : Measure W) [IsProbabilityMeasure π] (ψ : X → W → ℝ) (κ : ℝ) (hA : RFAssumptions ψ κ)
    (ρ : Measure (X × ℝ)) [IsProbabilityMeasure ρ] (hy : Integrable (fun p : X × ℝ => p.2) ρ)
    (L : Lp ℝ 2 ρ.fst →L[ℝ] Lp ℝ 2 ρ.fst)
    (hL : ∀ g : Lp ℝ 2 ρ.fst,
      (L g : X → ℝ) =ᵐ[ρ.fst] fun x => ∫ z, kernelOf π ψ x z * g z ∂ρ.fst)
    (fρ : X → ℝ) (hfρ2 : MemLp fρ 2 ρ.fst)
    (hfρ : ∀ s : Set X, MeasurableSet s → ∫ p in s ×ˢ Set.univ, p.2 ∂ρ = ∫ x in s, fρ x ∂ρ.fst)
    (M : ℕ) :
    let v : Lp ℝ 2 ρ.fst := (LinearMap.range L.toLinearMap)ᗮ.starProjection (hfρ2.toLp fρ)
    ∀ᵐ ω ∂(Measure.pi fun _ : Fin M => π),
      (∀ (n : ℕ) (z : Fin n → X × ℝ) (lam : ℝ), 0 < lam →
        ∫ x, (featureMap ψ ω x ⬝ᵥ
          ((empCov ψ ω z + lam • (1 : Matrix (Fin M) (Fin M) ℝ))⁻¹ *ᵥ
            featureAdjoint ψ ρ.fst ω v)) ^ 2 ∂ρ.fst = 0) ∧
      (∀ (n : ℕ) (z : Fin n → X × ℝ) (lam : ℝ), 0 < lam →
        ∫ x, rfEstimator ψ lam z ω x * v x ∂ρ.fst = 0) ∧
      (∀ β : Fin M → ℝ, ∫ x, (featureMap ψ ω x ⬝ᵥ β) * v x ∂ρ.fst = 0) := by sorry

end RFRidge.Basic
