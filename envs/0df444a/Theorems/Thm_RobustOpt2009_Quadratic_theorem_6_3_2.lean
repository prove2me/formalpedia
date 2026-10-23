-- Prove2me | Theorems.Thm_RobustOpt2009_Quadratic_theorem_6_3_2
-- name    : RobustOpt2009.Quadratic.theorem_6_3_2
-- status  : Disproved
-- author  : @Shuze Chen
-- created : 2026-10-22T03:42:14.417403+00:00
-- url     : https://prove2.me/theorems/f8befa84-9bd0-46c4-8053-3e8b53bd1407
-- title:
--   Theorem 6.3.2 — exact robust conic quadratic reformulations
-- statement:
--   Let $p,q$ be positive integers. Let $Z=\{\chi:\exists u,\ P\chi+Qu+c\in K\}$ be closed, as assumed in Section 5.1.2. Assume either that $K$ is a closed convex pointed cone and the representation is strictly feasible, or that $K$ is given by finitely many homogeneous linear inequalities. Let $A^n,b^n$ be nominal data and let $\sigma(y),\delta(y)$ be affine. The left and right perturbations are independent, and the left perturbation $\eta\in\mathbb R^{p\times q}$ has induced Euclidean norm at most one.
--
--   1. If $L(y)\in\mathbb R^{p\times k}$ is affine and $R\in\mathbb R^q$ is fixed and nonzero, the constraint $\|A^ny+b^n+L(y)^T\eta R\|_2\le\sigma(y)^T\chi+\delta(y)$ for all admissible $\eta,\chi$ holds exactly when there exist $\tau,v,\lambda$ satisfying
--   $$\tau+c^Tv\le\delta(y),\quad P^Tv=\sigma(y),\quad Q^Tv=0,\quad v\in K^*,$$
--   $$\begin{pmatrix}\tau I_k&L(y)^T&A^ny+b^n\\L(y)&\lambda I_p&0\\(A^ny+b^n)^T&0&\tau-\lambda R^TR\end{pmatrix}\succeq0.$$
--   2. If $L\in\mathbb R^{p\times k}$ is fixed and nonzero and $R(y)\in\mathbb R^q$ is affine, the analogous robust constraint holds exactly when the same right certificate and
--   $$\begin{pmatrix}\tau I_k-\lambda L^TL&0&A^ny+b^n\\0&\lambda I_q&R(y)\\(A^ny+b^n)^T&R(y)^T&\tau\end{pmatrix}\succeq0$$
--   hold for some $\tau,v,\lambda$.
--
--   These equivalences hold at every decision $y$ and describe projection onto the original decision space.
--
--   **Formalization Note** The theorem is a conjunction of both cases. Affine maps retain affine dependence on the decision. No strict positivity of $\tau$ or additional constraint on $\lambda$ is inserted. The perturbation row and column dimensions are positive; other coordinate dimensions may be zero. Coordinates are real and finite; Euclidean norms are explicit square roots of sums of squares. The source's conic offset vector $p$ is called $c$; its displayed multiplier is $v$, despite the introductory list saying $u$. The literal statement retains the absence of a nonemptiness premise in the polyhedral branch. Finding F6 gives an empty-set counterexample, so this faithful item is expected to be disproved. The separate corrected companion adds nonemptiness without changing the conclusion.
-- source:
--   Ben-Tal, El Ghaoui and Nemirovski, Robust Optimization, Princeton University Press, 2009, https://doi.org/10.1515/9781400831050, Theorem 6.3.2, with standing assumptions on printed pp. 160–161, printed p. 162 (PDF p. 188). Standing closedness convention: Section 5.1.2, printed p. 151 (PDF p. 177).

import Mathlib

open Matrix
open scoped BigOperators

namespace RobustOpt2009.Quadratic

/-- Theorem 6.3.2, printed p. 162: both exact projection identities.
The concrete sets and matrices are displayed here so the standalone blind audit
can read them without opening an imported definition. Perturbation dimensions
are positive, as required for the displayed LMIs to imply nonnegative multipliers.
Closed uncertainty is inherited from section 5.1.2 (printed p. 151).
The literal polyhedral case permits empty uncertainty; finding F6 records its failure. -/
theorem theorem_6_3_2 {n k p q m r s : ℕ} (hp : 0 < p) (hq : 0 < q)
    (K : Set (Fin m → ℝ)) (P : Matrix (Fin m) (Fin r) ℝ)
    (Q : Matrix (Fin m) (Fin s) ℝ) (c : Fin m → ℝ)
    (hclosed : IsClosed {χ : Fin r → ℝ | ∃ u, P *ᵥ χ + Q *ᵥ u + c ∈ K})
    (hreg :
      ((K.Nonempty ∧ (∀ z ∈ K, ∀ w ∈ K, z + w ∈ K) ∧
        (∀ z ∈ K, ∀ t : ℝ, 0 ≤ t → t • z ∈ K)) ∧
        (∀ z ∈ K, -z ∈ K → z = 0) ∧ IsClosed K ∧
        ∃ χ u, P *ᵥ χ + Q *ᵥ u + c ∈ interior K) ∨
      (∃ (h : ℕ) (H : Matrix (Fin h) (Fin m) ℝ),
        K = {z | ∀ i, 0 ≤ (H *ᵥ z) i}))
    (An : Matrix (Fin k) (Fin n) ℝ) (bn : Fin k → ℝ)
    (σ : (Fin n → ℝ) →ᵃ[ℝ] (Fin r → ℝ)) (δ : (Fin n → ℝ) →ᵃ[ℝ] ℝ) :
    let norm₂ : {d : ℕ} → (Fin d → ℝ) → ℝ := fun {_} x => Real.sqrt (∑ i, x i ^ 2)
    let Z : Set (Fin r → ℝ) := {χ | ∃ u, P *ᵥ χ + Q *ᵥ u + c ∈ K}
    (∀ (L : (Fin n → ℝ) →ᵃ[ℝ] Matrix (Fin p) (Fin k) ℝ)
      (R : Fin q → ℝ), R ≠ 0 → ∀ y : Fin n → ℝ,
      ((∀ η : Matrix (Fin p) (Fin q) ℝ,
        (∀ u : Fin q → ℝ, norm₂ (η *ᵥ u) ≤ norm₂ u) →
        ∀ χ ∈ Z, norm₂ (An *ᵥ y + bn + (L y)ᵀ *ᵥ (η *ᵥ R)) ≤ σ y ⬝ᵥ χ + δ y) ↔
        ∃ (τ : ℝ) (v : Fin m → ℝ) (lam : ℝ),
          (τ + c ⬝ᵥ v ≤ δ y ∧ Pᵀ *ᵥ v = σ y ∧ Qᵀ *ᵥ v = 0 ∧
            ∀ z ∈ K, 0 ≤ v ⬝ᵥ z) ∧
          (Matrix.fromBlocks
            (Matrix.fromBlocks (τ • (1 : Matrix (Fin k) (Fin k) ℝ)) (L y)ᵀ (L y)
              (lam • (1 : Matrix (Fin p) (Fin p) ℝ)))
            (fun i (_ : Unit) => Sum.elim (An *ᵥ y + bn) (fun _ => 0) i)
            (fun (_ : Unit) j => Sum.elim (An *ᵥ y + bn) (fun _ => 0) j)
            (fun (_ : Unit) (_ : Unit) => τ - lam * (R ⬝ᵥ R))).PosSemidef)) ∧
    (∀ (L : Matrix (Fin p) (Fin k) ℝ), L ≠ 0 →
      ∀ (R : (Fin n → ℝ) →ᵃ[ℝ] (Fin q → ℝ)) (y : Fin n → ℝ),
      ((∀ η : Matrix (Fin p) (Fin q) ℝ,
        (∀ u : Fin q → ℝ, norm₂ (η *ᵥ u) ≤ norm₂ u) →
        ∀ χ ∈ Z, norm₂ (An *ᵥ y + bn + Lᵀ *ᵥ (η *ᵥ R y)) ≤ σ y ⬝ᵥ χ + δ y) ↔
        ∃ (τ : ℝ) (v : Fin m → ℝ) (lam : ℝ),
          (τ + c ⬝ᵥ v ≤ δ y ∧ Pᵀ *ᵥ v = σ y ∧ Qᵀ *ᵥ v = 0 ∧
            ∀ z ∈ K, 0 ≤ v ⬝ᵥ z) ∧
          (Matrix.fromBlocks
            (Matrix.fromBlocks (τ • (1 : Matrix (Fin k) (Fin k) ℝ) - lam • (Lᵀ * L))
              (0 : Matrix (Fin k) (Fin q) ℝ) (0 : Matrix (Fin q) (Fin k) ℝ)
              (lam • (1 : Matrix (Fin q) (Fin q) ℝ)))
            (fun i (_ : Unit) => Sum.elim (An *ᵥ y + bn) (R y) i)
            (fun (_ : Unit) j => Sum.elim (An *ᵥ y + bn) (R y) j)
            (fun (_ : Unit) (_ : Unit) => τ)).PosSemidef)) := by sorry

end RobustOpt2009.Quadratic
