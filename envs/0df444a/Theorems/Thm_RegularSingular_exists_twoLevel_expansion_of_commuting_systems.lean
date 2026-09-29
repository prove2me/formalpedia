-- Prove2me | Theorems.Thm_RegularSingular_exists_twoLevel_expansion_of_commuting_systems
-- name    : RegularSingular.exists_twoLevel_expansion_of_commuting_systems
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.566428+00:00
-- url     : https://prove2.me/theorems/ce321364-669f-591b-aa31-9e0070511121
-- title:
--   Two-level corner expansion for commuting regular-singular systems
-- statement:
--   Fix naturals $n,J,R,d,d_2,d',d_2'$, an injective family of exponents $e:\mathrm{Fin}\,n\to\mathbb C$, reals $\rho$ and $\delta>0$ such that $\operatorname{Re}e_i\le\rho$ for all $i$, every shift $e_i+k$ ($k\in\mathbb N$) with real part $\le\rho$ occurs again in the family, and every shift $e_i+k$ with real part $>\rho$ has real part $\ge\rho+2\delta$; fix nonzero polynomials $q,q'\in\mathbb C[X]$ such that for each root $e_0$ of $q$ or of $q'$ and each $k\in\mathbb N$ the number $e_0+k$ belongs to the family when $\operatorname{Re}(e_0+k)\le\rho$ and satisfies $\operatorname{Re}(e_0+k)\ge\rho+2\delta$ otherwise, with $\deg q\le J$ and $n\deg q'\le J$. Let $P$ be a topological space and let $Mc(p,b)$, $Mc'(p,a)$ be $R\times R$ complex matrices and $A(p,k,b)$, $A'(p,k,a)$ continuous linear endomorphisms of $\mathbb C^R$ (indices $b\in\mathrm{Fin}(d_2+1)$, $a\in\mathrm{Fin}(d_2'+1)$, $k\in\mathrm{Fin}\,d$ resp. $\mathrm{Fin}\,d'$), all continuous in $p$ and bounded by $L$ in entries resp. operator norm, with $q\big(\sum_b z^b Mc(p,b)\big)=0$ for all $p$ and all real $z>0$ and $q'\big(\sum_a y^a Mc'(p,a)\big)=0$ for all $p$ and all real $y>0$. Let $Z\ge 2$ and let $F,F_y,F_z:P\times\mathbb R\times\mathbb R\to\mathbb C^R$ be such that $F$ is continuous on $P\times(0,1]\times(0,Z]$, for each $p$ and $z\in(0,Z]$, $y\in(0,1]$ the map $y\mapsto F(p,y,z)$ has derivative $F_y(p,y,z)$ and $$y\,F_y=\Big(\sum_b z^b Mc(p,b)\Big)F+\sum_{k}\sum_b y^{k+1}z^b A(p,k,b)F,$$ and symmetrically, for $y\in(0,1]$, $z\in(0,Z]$, the map $z\mapsto F(p,y,z)$ has derivative $F_z(p,y,z)$ with $z\,F_z=\big(\sum_a y^a Mc'(p,a)\big)F+\sum_k\sum_a z^{k+1}y^a A'(p,k,a)F$; finally $\|F(p,y,z)\|\le B\,y^{-m}z^{-m}$ on that range, for reals $m,B$. The conclusion asserts the existence of functions $c_{ij}:P\times\mathbb R\to\mathbb C^R$ ($i\in\mathrm{Fin}\,n$, $j\in\mathrm{Fin}\,J$), vectors $c^{(2)}_{ij,i'j'}:P\to\mathbb C^R$ and a constant $C$ such that each $c_{ij}$ is continuous on $P\times(0,Z]$, each $c^{(2)}_{ij,i'j'}$ is continuous, $\|c^{(2)}_{ij,i'j'}(p)\|\le C$, $\|c_{ij}(p,z)\|\le C z^{-m}$ for $z\in(0,Z]$, $$\Big\|F(p,y,z)-\sum_{i,j}y^{e_i}(\log y)^{j}c_{ij}(p,z)\Big\|\le C z^{-m}y^{\rho+\delta}\quad (z\in(0,Z],\ y\in(0,1]),$$ and, for $z$ restricted to $(0,1]$, $\big\|c_{ij}(p,z)-\sum_{i',j'}z^{e_{i'}}(\log z)^{j'}c^{(2)}_{ij,i'j'}(p)\big\|\le C z^{\rho+\delta}$.
--
--   This is the local structure of solutions of a compatible pair of regular-singular systems with polynomial coefficients at the normal crossing of the two singular divisors $y=0$ and $z=0$: the one-variable expansion in $y$, uniformly in the parameter $p$ and in $z$, whose coefficient functions themselves admit an expansion in $z$ along the same family of exponents, with second-level coefficients depending only on $p$. It is used in the cubic-induction step of the Langlands–Tunnell argument to produce joint asymptotic expansions of Whittaker-type functions from Casimir relations.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_RegularSingular_exists_twoLevel_expansion_of_commuting_systems.lean

import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.Topology.Instances.Matrix

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem RegularSingular.exists_twoLevel_expansion_of_commuting_systems
    {n J R d d₂ d' d₂' : ℕ} (e : Fin n → ℂ) (he : Function.Injective e) (ρ δ : ℝ) (hδ : 0 < δ)
    (hre : ∀ i, (e i).re ≤ ρ)
    (hcl : ∀ i (k : ℕ), (e i + k).re ≤ ρ → ∃ i', e i' = e i + k)
    (hgap : ∀ i (k : ℕ), ρ < (e i + k).re → ρ + 2 * δ ≤ (e i + k).re)
    (q q' : Polynomial ℂ) (hq : q ≠ 0) (hq' : q' ≠ 0)
    (hcov : ∀ e₀ : ℂ, q.IsRoot e₀ → ∀ k : ℕ, (e₀ + k).re ≤ ρ → ∃ i, e i = e₀ + k)
    (hcov' : ∀ e₀ : ℂ, q'.IsRoot e₀ → ∀ k : ℕ, (e₀ + k).re ≤ ρ → ∃ i, e i = e₀ + k)
    (hgq : ∀ e₀ : ℂ, q.IsRoot e₀ → ∀ k : ℕ, ρ < (e₀ + k).re → ρ + 2 * δ ≤ (e₀ + k).re)
    (hgq' : ∀ e₀ : ℂ, q'.IsRoot e₀ → ∀ k : ℕ, ρ < (e₀ + k).re → ρ + 2 * δ ≤ (e₀ + k).re)
    (hJ : q.natDegree ≤ J) (hJ' : n * q'.natDegree ≤ J)
    (P : Type*) [TopologicalSpace P]
    (Mc : P → Fin (d₂ + 1) → Matrix (Fin R) (Fin R) ℂ)
    (A : P → Fin d → Fin (d₂ + 1) → ((Fin R → ℂ) →L[ℂ] (Fin R → ℂ)))
    (Mc' : P → Fin (d₂' + 1) → Matrix (Fin R) (Fin R) ℂ)
    (A' : P → Fin d' → Fin (d₂' + 1) → ((Fin R → ℂ) →L[ℂ] (Fin R → ℂ)))
    (hMc : ∀ b, Continuous fun p => Mc p b) (hA : ∀ k b, Continuous fun p => A p k b)
    (hMc' : ∀ a, Continuous fun p => Mc' p a) (hA' : ∀ k a, Continuous fun p => A' p k a)
    (L : ℝ) (hMcL : ∀ p b i j, ‖Mc p b i j‖ ≤ L) (hAL : ∀ p k b, ‖A p k b‖ ≤ L)
    (hMcL' : ∀ p a i j, ‖Mc' p a i j‖ ≤ L) (hAL' : ∀ p k a, ‖A' p k a‖ ≤ L)
    (hq0 : ∀ p, ∀ z : ℝ, 0 < z → Polynomial.aeval (∑ b : Fin (d₂ + 1), ((z : ℂ) ^ (b : ℕ)) • Mc p b) q = 0)
    (hq0' : ∀ p, ∀ y : ℝ, 0 < y → Polynomial.aeval (∑ a : Fin (d₂' + 1), ((y : ℂ) ^ (a : ℕ)) • Mc' p a) q' = 0)
    (Z : ℝ) (hZ : 2 ≤ Z)
    (F Fy Fz : P → ℝ → ℝ → (Fin R → ℂ))
    (hF : ContinuousOn (fun w : P × ℝ × ℝ => F w.1 w.2.1 w.2.2) (Set.univ ×ˢ Set.Ioc 0 1 ×ˢ Set.Ioc 0 Z))
    (hsysY : ∀ p, ∀ z ∈ Set.Ioc (0 : ℝ) Z, ∀ y ∈ Set.Ioc (0 : ℝ) 1,
      HasDerivAt (fun y => F p y z) (Fy p y z) y ∧
      (y : ℂ) • Fy p y z =
        (fun i => ∑ j, (∑ b : Fin (d₂ + 1), (z : ℂ) ^ (b : ℕ) * Mc p b i j) • F p y z j) +
          ∑ k : Fin d, ∑ b : Fin (d₂ + 1), ((y : ℂ) ^ ((k : ℕ) + 1) * (z : ℂ) ^ (b : ℕ)) • A p k b (F p y z))
    (hsysZ : ∀ p, ∀ y ∈ Set.Ioc (0 : ℝ) 1, ∀ z ∈ Set.Ioc (0 : ℝ) Z,
      HasDerivAt (fun z => F p y z) (Fz p y z) z ∧
      (z : ℂ) • Fz p y z =
        (fun i => ∑ j, (∑ a : Fin (d₂' + 1), (y : ℂ) ^ (a : ℕ) * Mc' p a i j) • F p y z j) +
          ∑ k : Fin d', ∑ a : Fin (d₂' + 1), ((z : ℂ) ^ ((k : ℕ) + 1) * (y : ℂ) ^ (a : ℕ)) • A' p k a (F p y z))
    (m B : ℝ)
    (hbound : ∀ p, ∀ z ∈ Set.Ioc (0 : ℝ) Z, ∀ y ∈ Set.Ioc (0 : ℝ) 1, ‖F p y z‖ ≤ B * y ^ (-m) * z ^ (-m)) :
    ∃ (c : Fin n → Fin J → P → ℝ → (Fin R → ℂ)) (c₂ : Fin n → Fin J → Fin n → Fin J → P → (Fin R → ℂ))
      (C : ℝ),
      (∀ i j, ContinuousOn (fun w : P × ℝ => c i j w.1 w.2) (Set.univ ×ˢ Set.Ioc 0 Z)) ∧
      (∀ i j i' j', Continuous (c₂ i j i' j')) ∧
      (∀ p i j i' j', ‖c₂ i j i' j' p‖ ≤ C) ∧
      (∀ p i j, ∀ z ∈ Set.Ioc (0 : ℝ) Z, ‖c i j p z‖ ≤ C * z ^ (-m)) ∧
      (∀ p, ∀ z ∈ Set.Ioc (0 : ℝ) Z, ∀ y ∈ Set.Ioc (0 : ℝ) 1,
        ‖F p y z - ∑ i : Fin n, ∑ j : Fin J,
            ((y : ℂ) ^ e i * ((Real.log y : ℝ) : ℂ) ^ (j : ℕ)) • c i j p z‖ ≤ C * z ^ (-m) * y ^ (ρ + δ)) ∧
      (∀ p i j, ∀ z ∈ Set.Ioc (0 : ℝ) 1,
        ‖c i j p z - ∑ i' : Fin n, ∑ j' : Fin J,
            ((z : ℂ) ^ e i' * ((Real.log z : ℝ) : ℂ) ^ (j' : ℕ)) • c₂ i j i' j' p‖ ≤ C * z ^ (ρ + δ)) := by sorry
