-- Prove2me | Theorems.Thm_WLight_frickeFunction_modularity_package
-- name    : WLight.frickeFunction_modularity_package
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.37934+00:00
-- url     : https://prove2.me/theorems/409f428b-f096-5e14-b476-e6f5efd41901
-- title:
--   Fricke functions of level N: transformation and rationality package
-- statement:
--   Let $N$ be a natural number, nonzero as an instance, and let $L:\mathbb{H}\to$ `PeriodPair` assign to each $\tau$ a period pair with, by hypothesis, $\omega_1=\tau$ and $\omega_2=1$. For $a=(a_0,a_1)\in(\mathbb{Z}/N)^2$ put $f_a(\tau)=-\bigl(E_4(\tau)E_6(\tau)/\Delta(\tau)\bigr)/2592\cdot(2\pi i)^{-2}\,\wp_{L(\tau)}\bigl((\tilde a_0\tau+\tilde a_1)/N\bigr)$, where $\tilde a_i$ denotes the canonical representative in $[0,N)$. Eight assertions are conjoined. (1) For all $a$, all $\gamma\in\mathrm{SL}_2(\mathbb{Z})$ and all $\tau$, $f_a(\gamma\cdot\tau)=f_{a\bar\gamma}(\tau)$, with $a\bar\gamma$ the row vector $a$ multiplied on the right by the entrywise reduction of $\gamma$ modulo $N$. (2) $f_{-a}=f_a$ for all $a$. (3) For $a\neq0$, $f_a$ is holomorphic on $\mathbb{H}$. (4) For $a\neq0$, $f_a\cdot\Delta$ is bounded at $i\infty$. (5) For $a\neq0$, $f_a\cdot\Delta$ transported along `ofComplex` is periodic with period $N$, and every coefficient of its width-$N$ $q$-expansion lies in the subfield $\mathbb{Q}(e^{2\pi i/N})$ of $\mathbb{C}$. (6) For $a,b\neq0$, $f_a=f_b$ forces $b=a$ or $b=-a$. (7) For all $a$, $f_a(\gamma\cdot\tau)=f_a(\tau)$ for $\gamma$ in the principal congruence subgroup of level $N$. (8) If $s$ is coprime to $N$ and $\varphi:\mathbb{Q}(e^{2\pi i/N})\to\mathbb{C}$ is a ring homomorphism sending any element with complex value $e^{2\pi i/N}$ to $e^{2\pi i s/N}$, then for $a\neq0$ and each $n$, applying $\varphi$ to an element of the field whose complex value is the $n$-th $q$-expansion coefficient of $f_a\cdot\Delta$ yields the $n$-th coefficient of the $q$-expansion of $f_{(a_0,\,s\,a_1)}\cdot\Delta$.
--
--   This is the transformation and rationality theory of the Fricke functions of level $N$, the normalised values of $\wp$ at $N$-division points: their $\mathrm{SL}_2(\mathbb{Z})$-equivariance, evenness, injectivity up to sign, $\Gamma(N)$-invariance, cyclotomic width-$N$ expansions and the Galois conjugation of those expansions. It is the source of rational generators of the level-$N$ modular function field used in the construction of $\Gamma_1$-level cusp forms with prescribed coefficient fields and Galois behaviour.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WLight_frickeFunction_modularity_package.lean

import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Basic
import Mathlib.NumberTheory.ModularForms.Discriminant
import Mathlib.NumberTheory.ModularForms.QExpansion
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
import Mathlib.Geometry.Manifold.Notation
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open Complex Real
open UpperHalfPlane hiding I
open scoped Manifold MatrixGroups ModularForm

theorem WLight.frickeFunction_modularity_package (N : ℕ) [NeZero N]
    (L : ℍ → PeriodPair) (hL : ∀ τ : ℍ, (L τ).ω₁ = (τ : ℂ) ∧ (L τ).ω₂ = 1) :
    let f : (Fin 2 → ZMod N) → ℍ → ℂ := fun a τ =>
      -(ModularForm.E₄ τ * ModularForm.E₆ τ / ModularForm.discriminant τ) / 2592 *
        (((2 * π * I) ^ 2)⁻¹ *
          PeriodPair.weierstrassP (L τ)
            ((((a 0).val : ℂ) * (τ : ℂ) + ((a 1).val : ℂ)) / (N : ℂ)))

    (∀ (a : Fin 2 → ZMod N) (γ : SL(2, ℤ)) (τ : ℍ), f a (γ • τ) =
        f (Matrix.vecMul a ((γ : Matrix (Fin 2) (Fin 2) ℤ).map ((↑) : ℤ → ZMod N))) τ) ∧

    (∀ a : Fin 2 → ZMod N, f (-a) = f a) ∧

    (∀ a : Fin 2 → ZMod N, a ≠ 0 → MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (f a)) ∧

    (∀ a : Fin 2 → ZMod N, a ≠ 0 →
      IsBoundedAtImInfty (f a * ModularForm.discriminant)) ∧

    (∀ a : Fin 2 → ZMod N, a ≠ 0 →
      Function.Periodic ((f a * ModularForm.discriminant) ∘ ofComplex) N ∧
      ∀ n : ℕ, (qExpansion N (f a * ModularForm.discriminant)).coeff n ∈
        IntermediateField.adjoin ℚ {cexp (2 * π * I / N)}) ∧

    (∀ a b : Fin 2 → ZMod N, a ≠ 0 → b ≠ 0 → f a = f b → b = a ∨ b = -a) ∧

    (∀ a : Fin 2 → ZMod N, ∀ γ ∈ CongruenceSubgroup.Gamma N, ∀ τ : ℍ,
      f a (γ • τ) = f a τ) ∧

    (∀ s : ℕ, s.Coprime N →
      ∀ φ : ↑(IntermediateField.adjoin ℚ {cexp (2 * π * I / N)}) →+* ℂ,
        (∀ z : ↑(IntermediateField.adjoin ℚ {cexp (2 * π * I / N)}),
            (z : ℂ) = cexp (2 * π * I / N) → φ z = cexp (2 * π * I / N) ^ s) →
        ∀ a : Fin 2 → ZMod N, a ≠ 0 →
          ∀ (n : ℕ) (z : ↑(IntermediateField.adjoin ℚ {cexp (2 * π * I / N)})),
            (z : ℂ) = (qExpansion N (f a * ModularForm.discriminant)).coeff n →
            (qExpansion N (f ![a 0, (s : ZMod N) * a 1] * ModularForm.discriminant)).coeff n = φ z) := by sorry
