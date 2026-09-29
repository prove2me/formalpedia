-- Prove2me | Theorems.Thm_RegularSingular_exists_twoLevel_coeff_of_transport_of_slice_expansion
-- name    : RegularSingular.exists_twoLevel_coeff_of_transport_of_slice_expansion
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.566428+00:00
-- url     : https://prove2.me/theorems/41c65d7b-ab05-51a4-b976-a4d44077f284
-- title:
--   Transport of two-level exp–log expansions off a slice
-- statement:
--   Let $P$ be a locally compact, first countable topological space, let $n,J$ be naturals, let $e : \mathrm{Fin}\,n \to \mathbb{C}$ be injective, and let $\rho,\delta \in \mathbb{R}$ with $\delta > 0$ satisfy: $\operatorname{Re} e_i \le \rho$ for all $i$; for every $i$ and every natural $k$ with $\operatorname{Re}(e_i + k) \le \rho$ there is $i'$ with $e_{i'} = e_i + k$; and for every $i$ and natural $k$ with $\operatorname{Re}(e_i + k) > \rho$ one has $\operatorname{Re}(e_i + k) \ge \rho + 2\delta$. Let $S \subseteq P$ and let $W : \mathbb{R} \to \mathbb{R} \to P \to \mathbb{C}$ be continuous on $(0,\infty) \times (0,\infty) \times P$. Two hypotheses are imposed. Transport: for each compact $K \subseteq P$ there are $\lambda_0 \in (0,1]$, bounds $n_B, \Omega \ge 0$ and a compact $K_0 \subseteq S$ such that each $g \in K$ admits $\lambda,\tau \in [\lambda_0,\lambda_0^{-1}]$, reals $n_1,n_2$ with $|n_i| \le n_B$, $\kappa_1 \in \mathbb{C}$ with $\|\kappa_1\| \le \Omega$ and $k' \in K_0$ with $W(y_1,y_2,g) = \kappa_1 e^{2\pi i (y_1 n_1 + y_2 n_2)} W(\lambda y_1, \tau y_2, k')$ for all $y_1,y_2 > 0$. Slice expansion: for each compact $K_0 \subseteq S$ and each $Z \ge 2$ there are $m, C \in \mathbb{R}$, functions $c^S_{ij}(z,k)$ and $c^{(2)}_{ij,i'j'}(k)$ with $\|c^{(2)}_{ij,i'j'}(k)\| \le C$ and $\|c^S_{ij}(z,k)\| \le C z^{-m}$ for $k \in K_0$, $z \in (0,Z]$, such that for $k \in K_0$, $z \in (0,Z]$ and $y \in (0,1]$ one has $\|W(y,z,k) - \sum_{i,j} c^S_{ij}(z,k)\, y^{e_i} (\log y)^j\| \le C z^{-m} y^{\rho+\delta}$, and for $z \in (0,1]$ one has $\|c^S_{ij}(z,k) - \sum_{i',j'} c^{(2)}_{ij,i'j'}(k)\, z^{e_{i'}} (\log z)^{j'}\| \le C z^{\rho+\delta}$. The conclusion asserts the existence of $c_{ij} : \mathbb{R} \to P \to \mathbb{C}$, each continuous on $\{(y_2,p) : y_2 > 0\}$, such that for every compact $K \subseteq P$ and every $b \ge 1$ there is $C$ with $\|W(y_1,y_2,k) - \sum_{i,j} c_{ij}(y_2,k)\, y_1^{e_i} (\log y_1)^j\| \le C y_1^{\rho+\delta}$ for all $k \in K$, $y_2 \in [b^{-1},b]$ and $y_1 \in (0,1]$; and moreover of continuous functions $c'_{ij,i'j'} : P \to \mathbb{C}$ such that for every compact $K \subseteq P$ there is $C$ with $\|c_{ij}(y_2,k) - \sum_{i',j'} c'_{ij,i'j'}(k)\, y_2^{e_{i'}} (\log y_2)^{j'}\| \le C y_2^{\rho+\delta}$ for all $k \in K$, all $i,j$ and all $y_2 \in (0,1]$.
--
--   This is the globalisation step for two-variable asymptotic expansions of regular–singular type: expansions with exponents $y^{e_i}(\log y)^j$ known only on a compact slice, together with a rescaling-and-exponential-twist transport identity, are propagated to the whole parameter space with coefficients that are continuous in the second variable and the parameter and that themselves admit an exp–log expansion of the same shape. It feeds the construction of joint asymptotic expansions for Whittaker-type functions along the diagonal used in the Langlands–Tunnell cubic induction.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_RegularSingular_exists_twoLevel_coeff_of_transport_of_slice_expansion.lean

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Topology.Compactness.LocallyCompact

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem RegularSingular.exists_twoLevel_coeff_of_transport_of_slice_expansion
    {P : Type*} [TopologicalSpace P] [LocallyCompactSpace P] [FirstCountableTopology P]
    {n J : ℕ} (e : Fin n → ℂ) (he : Function.Injective e) (ρ δ : ℝ) (hδ : 0 < δ)
    (hre : ∀ i, (e i).re ≤ ρ)
    (hcl : ∀ i (k : ℕ), (e i + k).re ≤ ρ → ∃ i', e i' = e i + k)
    (hgap : ∀ i (k : ℕ), ρ < (e i + k).re → ρ + 2 * δ ≤ (e i + k).re)
    (S : Set P) (W : ℝ → ℝ → P → ℂ)
    (hWc : ContinuousOn (fun w : ℝ × ℝ × P => W w.1 w.2.1 w.2.2) (Set.Ioi 0 ×ˢ Set.Ioi 0 ×ˢ Set.univ))
    (htrans : ∀ K : Set P, IsCompact K → ∃ (lam₀ nB Ω : ℝ) (K₀ : Set P), 0 < lam₀ ∧ lam₀ ≤ 1 ∧ 0 ≤ nB ∧
      0 ≤ Ω ∧ IsCompact K₀ ∧ K₀ ⊆ S ∧ ∀ g ∈ K, ∃ (lam τ n₁ n₂ : ℝ) (κ₁ : ℂ) (k' : P), k' ∈ K₀ ∧
        lam₀ ≤ lam ∧ lam ≤ lam₀⁻¹ ∧ lam₀ ≤ τ ∧ τ ≤ lam₀⁻¹ ∧ |n₁| ≤ nB ∧ |n₂| ≤ nB ∧ ‖κ₁‖ ≤ Ω ∧
        ∀ y₁ y₂ : ℝ, 0 < y₁ → 0 < y₂ →
          W y₁ y₂ g = κ₁ * Complex.exp (2 * Real.pi * Complex.I * ((y₁ * n₁ + y₂ * n₂ : ℝ) : ℂ)) *
            W (lam * y₁) (τ * y₂) k')
    (hslice : ∀ K₀ : Set P, IsCompact K₀ → K₀ ⊆ S → ∀ Z : ℝ, 2 ≤ Z →
      ∃ (m C : ℝ) (cS : Fin n → Fin J → ℝ → P → ℂ) (c₂ : Fin n → Fin J → Fin n → Fin J → P → ℂ),
        (∀ k ∈ K₀, ∀ i j i' j', ‖c₂ i j i' j' k‖ ≤ C) ∧
        (∀ k ∈ K₀, ∀ z ∈ Set.Ioc (0 : ℝ) Z, ∀ i j, ‖cS i j z k‖ ≤ C * z ^ (-m)) ∧
        (∀ k ∈ K₀, ∀ z ∈ Set.Ioc (0 : ℝ) Z, ∀ y ∈ Set.Ioc (0 : ℝ) 1,
          ‖W y z k - ∑ i : Fin n, ∑ j : Fin J,
              cS i j z k * ((y : ℂ) ^ e i * ((Real.log y : ℝ) : ℂ) ^ (j : ℕ))‖ ≤ C * z ^ (-m) * y ^ (ρ + δ)) ∧
        (∀ k ∈ K₀, ∀ i j, ∀ z ∈ Set.Ioc (0 : ℝ) 1,
          ‖cS i j z k - ∑ i' : Fin n, ∑ j' : Fin J,
              c₂ i j i' j' k * ((z : ℂ) ^ e i' * ((Real.log z : ℝ) : ℂ) ^ (j' : ℕ))‖ ≤ C * z ^ (ρ + δ))) :
    ∃ c : Fin n → Fin J → ℝ → P → ℂ,
      (∀ i j, ContinuousOn (fun p : ℝ × P => c i j p.1 p.2) {p | 0 < p.1}) ∧
      (∀ K : Set P, IsCompact K → ∀ b : ℝ, 1 ≤ b → ∃ C : ℝ, ∀ k ∈ K, ∀ y₂ : ℝ, b⁻¹ ≤ y₂ → y₂ ≤ b →
        ∀ y₁ : ℝ, 0 < y₁ → y₁ ≤ 1 →
        ‖W y₁ y₂ k - ∑ i : Fin n, ∑ j : Fin J,
            c i j y₂ k * ((y₁ : ℂ) ^ e i * ((Real.log y₁ : ℝ) : ℂ) ^ (j : ℕ))‖ ≤ C * y₁ ^ (ρ + δ)) ∧
      ∃ c' : Fin n → Fin J → Fin n → Fin J → P → ℂ,
        (∀ i j i' j', Continuous (c' i j i' j')) ∧
        ∀ K : Set P, IsCompact K → ∃ C : ℝ, ∀ k ∈ K, ∀ (i : Fin n) (j : Fin J), ∀ y₂ : ℝ, 0 < y₂ → y₂ ≤ 1 →
          ‖c i j y₂ k - ∑ i' : Fin n, ∑ j' : Fin J,
              c' i j i' j' k * ((y₂ : ℂ) ^ e i' * ((Real.log y₂ : ℝ) : ℂ) ^ (j' : ℕ))‖ ≤ C * y₂ ^ (ρ + δ) := by sorry
