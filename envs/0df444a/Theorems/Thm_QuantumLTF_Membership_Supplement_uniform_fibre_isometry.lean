-- Prove2me | Theorems.Thm_QuantumLTF_Membership_Supplement_uniform_fibre_isometry
-- name    : QuantumLTF.Membership.Supplement.uniform_fibre_isometry
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-24T23:22:18.748797+00:00
-- url     : https://prove2.me/theorems/1eb3a3bd-bfd8-4687-99ed-68af2c93bee3
-- title:
--   Uniform finite-fibre isometry for occupation decoding
-- statement:
--   Let $f:X\to Y$ be a surjection between finite sets. There is a fixed complex linear isometry $J$ from amplitudes on $Y$ to amplitudes on $X$ with
--
--   $$(J\psi)(x)=\frac{\psi(f(x))}{\sqrt{|f^{-1}(f(x))|}}.$$
--
--   Every amplitude function constant on each fibre belongs to the image of $J$. This algebraic fact underlies occupation decoding in Theorem 5.4: tensor-product amplitudes depend only on occupation counts. It asserts an isometry and its image property; the efficient circuit implementation remains a separate construction.
-- source:
--   Krivcenko, Nguyen, de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, https://arxiv.org/html/2609.40331v3, Section 5.3, Theorem 5.4, occupation-to-tensor isometry (algebraic finite-fibre component).

import Mathlib

theorem QuantumLTF.Membership.Supplement.uniform_fibre_isometry {X Y : Type*} [Fintype X] [Fintype Y]
    (f : X → Y) (hf : Function.Surjective f) :
    ∃ J : EuclideanSpace ℂ Y →ₗᵢ[ℂ] EuclideanSpace ℂ X,
      (∀ (ψ : EuclideanSpace ℂ Y) (x : X),
        J ψ x = ψ (f x)/(Real.sqrt (Nat.card {x' : X // f x' = f x}):ℂ)) ∧
      ∀ g : X → ℂ, (∀ x x', f x = f x' → g x = g x') →
        ∃ ψ : EuclideanSpace ℂ Y, J ψ = WithLp.toLp 2 g := by sorry
