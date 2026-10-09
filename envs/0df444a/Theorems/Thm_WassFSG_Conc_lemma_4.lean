-- Prove2me | Theorems.Thm_WassFSG_Conc_lemma_4
-- name    : WassFSG.Conc.lemma_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T09:50:25.337965+00:00
-- url     : https://prove2.me/theorems/992c634d-9b27-46d7-9b57-826e397fe30e
-- title:
--   Lemma 4 — tensorization: P ∈ T_p(τ) implies P^⊗n ∈ T_p(τ n^{2/p−1}) for the ℓ_p product distance
-- statement:
--   Let $\mathcal Z$ be a separable Banach space, $p\in[1,2]$, $\tau>0$ and $n\ge1$. Equip $\mathcal Z^n$ with the product distance
--   $$\mathsf d_p(z,\tilde z)=\Big(\sum_{i=1}^n\|z_i-\tilde z_i\|^p\Big)^{1/p}.$$
--   If $\mathbb P\in\mathcal P_p(\mathcal Z)$ satisfies the transportation-information inequality $T_p(\tau)$, then the $n$-fold product $\mathbb P_\otimes=\mathbb P^{\otimes n}$ satisfies $T_p(\tau n^{2/p-1})$ on $(\mathcal Z^n,\mathsf d_p)$: for every $\mu\in\mathcal P_p(\mathcal Z^n)$,
--   $$\mathcal W_p(\mu,\mathbb P_\otimes)\le\sqrt{\tau\,n^{2/p-1}\,H(\mu\|\mathbb P_\otimes)},$$
--   where $\mathcal W_p$ is the Wasserstein distance of order $p$ for $\mathsf d_p$.
--
--   This is the dimension-dependent tensorization of transportation inequalities: for $p=2$ the constant does not grow with $n$, for $p=1$ it grows linearly. It is the input to the concentration Lemma 5.
--
--   **Formalization Note** $\mathcal P_p(\mathcal Z^n)$ is the class of probability measures with $\mathbb E[\sum_i\|z_i\|^p]<\infty$, and $T_p$ on $\mathcal Z^n$ is the same definition as on $\mathcal Z$ with the cost $\sum_i\|z_i-\tilde z_i\|^p$. The hypothesis $n\ge1$ is added (the paper's $n$ is a sample size). $\mathcal Z$ is assumed complete, separable and Borel.
-- source:
--   Gao, Finite-Sample Guarantees for Wasserstein Distributionally Robust Optimization: Breaking the Curse of Dimensionality, arXiv:2009.04382, Lemma 4, p. 21 (product distance d_p defined on p. 20)

import Mathlib
import Definitions.Def_WassFSG_Conc_Setting

namespace WassFSG.Conc

open MeasureTheory
open scoped ENNReal

/-- Lemma 4 (p. 21): for `p ∈ [1, 2]`, if `P ∈ 𝒫_p(Z)` satisfies `T_p(τ)`, then the `n`-fold product
`P_⊗` satisfies `T_p(τ n^{2/p - 1})` on `Z^n` with the product distance
`d_p(z, z̃) = (∑ᵢ ‖zᵢ - z̃ᵢ‖^p)^{1/p}` (p. 20). -/
theorem lemma_4 {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [CompleteSpace Z]
    [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z]
    (n : ℕ) (hn : 0 < n) (p τ : ℝ) (hp1 : 1 ≤ p) (hp2 : p ≤ 2) (hτ : 0 < τ)
    (P : Measure Z) (hP : Tp p τ P) :
    TpProd n p (τ * (n : ℝ) ^ (2 / p - 1)) (Measure.pi fun _ : Fin n => P) := by sorry

end WassFSG.Conc
