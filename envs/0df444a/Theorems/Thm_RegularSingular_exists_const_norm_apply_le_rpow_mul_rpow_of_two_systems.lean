-- Prove2me | Theorems.Thm_RegularSingular_exists_const_norm_apply_le_rpow_mul_rpow_of_two_systems
-- name    : RegularSingular.exists_const_norm_apply_le_rpow_mul_rpow_of_two_systems
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.566428+00:00
-- url     : https://prove2.me/theorems/58ca299b-b3d4-5795-b389-8a89777069eb
-- title:
--   Uniform two-variable decay for compatible regular singular systems
-- statement:
--   Let $E$ be a complex Banach space, let $r,d,d'$ be natural numbers, let $q,q'$ be nonzero polynomials over $\mathbb{C}$, let $i_0 < r$, and let $L,m,m',\tau,\theta$ be reals with $\theta < \tau$. Then there is a real $\kappa$ — depending only on these data, and in particular on none of the objects quantified below — such that the following holds for all $M,M' : \mathbb{R} \to \mathrm{Mat}_{r\times r}(\mathbb{C})$ and all families $A : \mathbb{R} \to (\mathrm{Fin}\,d \to \mathrm{End}^{\mathrm{cont}}_{\mathbb{C}}(E^r))$, $A' : \mathbb{R} \to (\mathrm{Fin}\,d' \to \mathrm{End}^{\mathrm{cont}}_{\mathbb{C}}(E^r))$ of bounded operators on $E^r$. Assume: every entry of $M(z)$ and of $M'(y)$, and every operator norm $\|A(z)_k\|$, $\|A'(y)_k\|$, is at most $L$ for all $y,z \in (0,1]$; and $q(M(z)) = 0$, $q'(M'(y)) = 0$ for all $z,y \in (0,1]$. Then for all $F, F_y, F_z : \mathbb{R} \to \mathbb{R} \to E^r$ and every real $B$, if for all $y,z \in (0,1]$ the map $y \mapsto F(y,z)$ has derivative $F_y(y,z)$ at $y$ with $y\,F_y(y,z) = \big(\sum_j M(z)_{ij}\cdot F(y,z)_j\big)_i + \sum_{k<d} y^{k+1} A(z)_k(F(y,z))$, and the map $z \mapsto F(y,z)$ has derivative $F_z(y,z)$ at $z$ with $z\,F_z(y,z) = \big(\sum_j M'(y)_{ij}\cdot F(y,z)_j\big)_i + \sum_{k<d'} z^{k+1} A'(y)_k(F(y,z))$; if $\|F(y,z)\| \le B\,y^{-m} z^{-m'}$ for all $y,z \in (0,1]$; if for each fixed $z \in (0,1]$ there is a constant $C$ with $\|F(y,z)_{i_0}\| \le C\,y^{\tau}$ for all $y \in (0,1]$; and if for each fixed $y \in (0,1]$ there is a constant $C$ with $\|F(y,z)_{i_0}\| \le C\,z^{\tau}$ for all $z \in (0,1]$; then $\|F(y,z)_{i_0}\| \le \kappa\,B\,(y^{\theta} z^{\theta})$ for all $y,z \in (0,1]$. All real powers here are `Real.rpow`.
--
--   This is a uniform two-variable decay estimate for a pair of compatible systems with regular singularity at the boundary of the unit square: separate one-variable decay of order $\tau$ in each variable, together with a crude joint bound $B\,y^{-m}z^{-m'}$, upgrades to joint decay of any order $\theta < \tau$ with a constant $\kappa B$ in which $\kappa$ is independent of the systems, of $F$ and of $B$. It is used in the Langlands–Tunnell part of the development, in [`LanglandsTunnell.CubicInduction.exists_forall_isCompact_orth3_norm_whittaker3_le_of_systems`](thm.html#LanglandsTunnell.CubicInduction.exists_forall_isCompact_orth3_norm_whittaker3_le_of_systems), to obtain uniform decay of Whittaker-type functions on a compact family.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_RegularSingular_exists_const_norm_apply_le_rpow_mul_rpow_of_two_systems.lean

import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.Topology.Instances.Matrix

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v

theorem RegularSingular.exists_const_norm_apply_le_rpow_mul_rpow_of_two_systems
    (E : Type u) [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (r d d' : ℕ) (q q' : Polynomial ℂ) (hq : q ≠ 0) (hq' : q' ≠ 0) (i₀ : Fin r) (L m m' τ θ : ℝ) (hθ : θ < τ) :
    ∃ κ : ℝ, ∀ (M M' : ℝ → Matrix (Fin r) (Fin r) ℂ) (A : ℝ → Fin d → ((Fin r → E) →L[ℂ] (Fin r → E)))
      (A' : ℝ → Fin d' → ((Fin r → E) →L[ℂ] (Fin r → E))),
      (∀ z ∈ Set.Ioc (0 : ℝ) 1, ∀ i j, ‖M z i j‖ ≤ L) → (∀ y ∈ Set.Ioc (0 : ℝ) 1, ∀ i j, ‖M' y i j‖ ≤ L) →
      (∀ z ∈ Set.Ioc (0 : ℝ) 1, ∀ k, ‖A z k‖ ≤ L) → (∀ y ∈ Set.Ioc (0 : ℝ) 1, ∀ k, ‖A' y k‖ ≤ L) →
      (∀ z ∈ Set.Ioc (0 : ℝ) 1, Polynomial.aeval (M z) q = 0) →
      (∀ y ∈ Set.Ioc (0 : ℝ) 1, Polynomial.aeval (M' y) q' = 0) →
      ∀ (F Fy Fz : ℝ → ℝ → (Fin r → E)) (B : ℝ),
      (∀ z ∈ Set.Ioc (0 : ℝ) 1, ∀ y ∈ Set.Ioc (0 : ℝ) 1, HasDerivAt (fun y => F y z) (Fy y z) y ∧
        (y : ℂ) • Fy y z =
          (fun i => ∑ j, M z i j • F y z j) + ∑ k : Fin d, ((y : ℂ) ^ ((k : ℕ) + 1)) • A z k (F y z)) →
      (∀ y ∈ Set.Ioc (0 : ℝ) 1, ∀ z ∈ Set.Ioc (0 : ℝ) 1, HasDerivAt (fun z => F y z) (Fz y z) z ∧
        (z : ℂ) • Fz y z =
          (fun i => ∑ j, M' y i j • F y z j) + ∑ k : Fin d', ((z : ℂ) ^ ((k : ℕ) + 1)) • A' y k (F y z)) →
      (∀ y ∈ Set.Ioc (0 : ℝ) 1, ∀ z ∈ Set.Ioc (0 : ℝ) 1, ‖F y z‖ ≤ B * y ^ (-m) * z ^ (-m')) →
      (∀ z ∈ Set.Ioc (0 : ℝ) 1, ∃ C : ℝ, ∀ y ∈ Set.Ioc (0 : ℝ) 1, ‖F y z i₀‖ ≤ C * y ^ τ) →
      (∀ y ∈ Set.Ioc (0 : ℝ) 1, ∃ C : ℝ, ∀ z ∈ Set.Ioc (0 : ℝ) 1, ‖F y z i₀‖ ≤ C * z ^ τ) →
      ∀ y ∈ Set.Ioc (0 : ℝ) 1, ∀ z ∈ Set.Ioc (0 : ℝ) 1, ‖F y z i₀‖ ≤ κ * B * (y ^ θ * z ^ θ) := by sorry
