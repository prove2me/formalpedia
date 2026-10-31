-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P47_attained_minimum_differentiation
-- name    : QAlgorithms.Papers.Independent.Intake100.P47.attained_minimum_differentiation
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T13:37:22.64918+00:00
-- url     : https://prove2.me/theorems/5b6083db-a1e9-4323-ac0f-c8fa5746674a
-- title:
--   Lemma 24: Differentiation of an attained minimum
-- statement:
--   All Hilbert spaces are finite dimensional and nonzero. States are positive semidefinite operators of trace one, logarithms are natural, and $\rho\ll\sigma$ means inclusion of supports. Write $D_\alpha$ and $\widetilde D_\alpha$ for the Petz and sandwiched divergences, respectively, with generalized inverse powers on support and orders $0,1,\infty$ defined by limits. Let $X$ be a real Banach space, $Y=\mathbb R^m$ with $m\in\mathbb N$, $\Omega\subset\Omega'\subset X$ with $\Omega'$ open, and $\Gamma\subset Y$ open and convex. Let $f:\Omega'\times\Gamma\to\mathbb R$ be twice continuously Fréchet differentiable, with positive definite Hessian in $y$ for every $x\in\Omega,y\in\Gamma$. Suppose a global minimum in $\Gamma$ is attained for each $x\in\Omega$. Define $\bar y(x)=\arg\min_{y\in\Gamma}f(x,y)$ and $g(x)=\inf_{y\in\Gamma}f(x,y)$. Near each $x_0\in\Omega$ there is an open neighborhood $V\subset\Omega'$ and a $C^1$ function $G:V\to\mathbb R$ such that
--   $$G(x)=g(x),\qquad DG(x)=D_Xf(x,\bar y(x))\quad(x\in V\cap\Omega).$$
--   The minimizer and value are constructed from $f$. This local-extension interpretation follows the proof's implicit-function argument and accommodates a nonopen $\Omega$ without choosing a nonunique within-derivative.
-- source:
--   Correlation Detection and an Operational Interpretation of the Renyi Mutual Information, arXiv:1408.6894v5, PDF p. 28, Lemma 24: Differentiation of an attained minimum

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P47

noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P47

open scoped BigOperators Matrix ComplexOrder ComplexConjugate Topology

open Filter QAlgorithms

open QAlgorithms.Papers.Independent.Information100.P22 (Op mixed)

open QAlgorithms.Papers.Independent.Information100.P60 (copies)

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower)

open QAlgorithms.Papers.Independent.Dependency50.P28 (SupportLE pinch logNonnegativeExtended)

open QAlgorithms.Papers.Independent.Dependency50.P21 (relativeEntropy IsSupported)

open QAlgorithms.Papers.Independent.Bridge50.P49 (groupedProduct)

open QAlgorithms.Papers.Independent.Claimed50.P12 (DiagonalIn)

attribute [local instance] Classical.propDecidable Classical.decEq

variable {A B C D I J : Type}

variable [Fintype A] [Fintype B] [Fintype C] [Fintype D] [Fintype I] [Fintype J]

variable [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq D]

variable [DecidableEq I] [DecidableEq J]

/-- arXiv:1408.6894v5, PDF p.28, Lemma 24.
Omega need not be open: near each point the value has a C1 extension agreeing
on Omega, with the stated partial derivative there. This avoids a canonical
within-derivative on thin sets. The Hessian is positive on every nonzero Y direction. -/
theorem attained_minimum_differentiation
    {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (m : ℕ) (Omega OmegaOpen : Set X) (Gamma : Set (EuclideanSpace ℝ (Fin m)))
    (hOpen : IsOpen OmegaOpen) (hSub : Omega ⊆ OmegaOpen)
    (hGamma : IsOpen Gamma) (hc : Convex ℝ Gamma)
    (f : X × EuclideanSpace ℝ (Fin m) → ℝ)
    (hC2 : ContDiffOn ℝ 2 f (OmegaOpen ×ˢ Gamma))
    (hHess : ∀ x ∈ Omega, ∀ y ∈ Gamma, ∀ v : EuclideanSpace ℝ (Fin m), v ≠ 0 →
      0 < (fderiv ℝ (fun y => fderiv ℝ (fun z => f (x,z)) y) y) v v)
    (hatt : ∀ x ∈ Omega, ∃ y ∈ Gamma, ∀ z ∈ Gamma, f (x,y) ≤ f (x,z)) :
    ∀ x0 ∈ Omega, ∃ V : Set X, IsOpen V ∧ x0 ∈ V ∧ V ⊆ OmegaOpen ∧
      ∃ g : X → ℝ, ContDiffOn ℝ 1 g V ∧
        (∀ x ∈ V ∩ Omega, g x = attainedValueInfimum f Gamma x) ∧
        (∀ x ∈ V ∩ Omega,
          HasFDerivAt g (fderiv ℝ (fun z => f (z,minimizer f Gamma x)) x) x) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P47

end
