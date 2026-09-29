-- Prove2me | Theorems.Thm_RegularSingular_exists_logDepth_le_natDegree_norm_sub_expansion_le
-- name    : RegularSingular.exists_logDepth_le_natDegree_norm_sub_expansion_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.566428+00:00
-- url     : https://prove2.me/theorems/62e6ba53-f150-5a2a-a830-26cef4eef37e
-- title:
--   Logarithmic depth at most deg q in regular-singular expansions
-- statement:
--   For every nonzero $q \in \mathbb{C}[X]$ there is a natural number $D \le \deg q$ with the following property. Let $E$ be a complex Banach space, let $r, d \in \mathbb{N}$ and let $L, m, \rho, \theta \in \mathbb{R}$ be such that $\theta < \operatorname{Re}(e+n)$ whenever $e$ is a root of $q$, $n \in \mathbb{N}$ and $\rho < \operatorname{Re}(e+n)$. Then there are a finite set $S \subseteq \mathbb{C}$, each of whose elements $\mu$ satisfies $\operatorname{Re}\mu \le \rho$ and has the form $\mu = e+n$ with $q(e)=0$ and $n \in \mathbb{N}$, and a real constant $\kappa$, such that for every topological space $P$, every $M : P \to \mathrm{M}_r(\mathbb{C})$ and every $A : P \to (\mathrm{Fin}\,d \to \mathcal{L}(E^r))$ with $M$ continuous, $\|M(p)_{ij}\| \le L$, $q(M(p)) = 0$ for all $p$, each $p \mapsto A(p)_k$ continuous and $\|A(p)_k\| \le L$, the following holds. Let $F, F' : P \to \mathbb{R} \to E^r$ and $B : P \to \mathbb{R}$ be such that $(p,y) \mapsto F(p)(y)$ is continuous on $\mathrm{univ} \times (0,1]$, $B$ is locally bounded above (each $p_0$ has a neighbourhood on which $B \le B_0$ for some $B_0$), for all $p$ and all $y \in (0,1]$ the map $F(p)$ is differentiable at $y$ with derivative $F'(p)(y)$ and $$y\,F'(p)(y) = \Big(i \mapsto \sum_j M(p)_{ij} \cdot F(p)(y)_j\Big) + \sum_{k<d} y^{k+1}\, A(p)_k\big(F(p)(y)\big),$$ and $\|F(p)(y)\| \le B(p)\, y^{-m}$ for $y \in (0,1]$. Then there exists $c : \mathbb{C} \to \mathbb{N} \to P \to E^r$ with each $c_{\mu,j}$ continuous on $P$, such that for every $p$: $\|c_{\mu,j}(p)\| \le \kappa B(p)$ for all $\mu, j$; $c_{\mu,j}(p) = 0$ for $\mu \in S$ with $\operatorname{Re}\mu < -m$ and all $j$; and $$\Big\| F(p)(y) - \sum_{\mu \in S} \sum_{j < D} y^{\mu} (\log y)^j\, c_{\mu,j}(p) \Big\| \le \kappa\, B(p)\, y^{\theta} \quad (0 < y \le 1).$$
--
--   This is a Frobenius-type asymptotic expansion, uniform in a topological parameter space, for a first-order system with a regular singularity at $y = 0$ whose residue matrix is annihilated by $q$ and which is perturbed by a tail $\sum_k y^{k+1} A_k$ of bounded operators on $E^r$; the point of the formulation is that the number $D$ of logarithmic powers needed, and hence the shape of the expansion, depends only on $q$, while the exponents lie among the shifts $e+n$ of roots of $q$ and the constants are bounded by $\kappa B(p)$. It is used in the Langlands–Tunnell part of the development, where expansions of Whittaker functions and of ratio coefficients for flat regular-singular systems are extracted from Casimir relations.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_RegularSingular_exists_logDepth_le_natDegree_norm_sub_expansion_le.lean

import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.Topology.Instances.Matrix

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v

theorem RegularSingular.exists_logDepth_le_natDegree_norm_sub_expansion_le (q : Polynomial ℂ) (hq : q ≠ 0) :
    ∃ D : ℕ, D ≤ q.natDegree ∧
      ∀ (E : Type u) [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] (r d : ℕ) (L m ρ θ : ℝ),
        (∀ e : ℂ, q.IsRoot e → ∀ n : ℕ, ρ < (e + n).re → θ < (e + n).re) →
    ∃ (S : Finset ℂ) (κ : ℝ),
      (∀ μ ∈ S, μ.re ≤ ρ ∧ ∃ (e : ℂ) (n : ℕ), q.IsRoot e ∧ μ = e + n) ∧
      ∀ (P : Type v) [TopologicalSpace P] (M : P → Matrix (Fin r) (Fin r) ℂ)
        (A : P → Fin d → ((Fin r → E) →L[ℂ] (Fin r → E))),
        Continuous M → (∀ p i j, ‖M p i j‖ ≤ L) → (∀ p, Polynomial.aeval (M p) q = 0) →
        (∀ k, Continuous fun p => A p k) → (∀ p k, ‖A p k‖ ≤ L) →
        ∀ (F F' : P → ℝ → (Fin r → E)) (B : P → ℝ),
        ContinuousOn (fun w : P × ℝ => F w.1 w.2) (Set.univ ×ˢ Set.Ioc 0 1) →
        (∀ p₀ : P, ∃ B₀ : ℝ, ∀ᶠ p in nhds p₀, B p ≤ B₀) →
        (∀ p, ∀ y ∈ Set.Ioc (0 : ℝ) 1, HasDerivAt (F p) (F' p y) y ∧
          (y : ℂ) • F' p y =
            (fun i => ∑ j, M p i j • F p y j) + ∑ k : Fin d, ((y : ℂ) ^ ((k : ℕ) + 1)) • A p k (F p y)) →
        (∀ p, ∀ y ∈ Set.Ioc (0 : ℝ) 1, ‖F p y‖ ≤ B p * y ^ (-m)) →
        ∃ c : ℂ → ℕ → P → (Fin r → E),
          (∀ μ j, Continuous (c μ j)) ∧
          ∀ p, (∀ μ j, ‖c μ j p‖ ≤ κ * B p) ∧ (∀ μ ∈ S, μ.re < -m → ∀ j, c μ j p = 0) ∧
            ∀ y ∈ Set.Ioc (0 : ℝ) 1,
              ‖F p y - ∑ μ ∈ S, ∑ j ∈ Finset.range D,
                  ((y : ℂ) ^ μ * ((Real.log y : ℝ) : ℂ) ^ j) • c μ j p‖ ≤ κ * B p * y ^ θ := by sorry
