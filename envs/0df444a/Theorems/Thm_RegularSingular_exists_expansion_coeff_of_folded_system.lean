-- Prove2me | Theorems.Thm_RegularSingular_exists_expansion_coeff_of_folded_system
-- name    : RegularSingular.exists_expansion_coeff_of_folded_system
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.566428+00:00
-- url     : https://prove2.me/theorems/a31c68bd-146e-506d-86e1-06b56bb1ca0b
-- title:
--   Parameter-uniform expansion for folded regular-singular systems
-- statement:
--   Fix naturals $n, J, R, d_2, d$, an injective family of exponents $e : \mathrm{Fin}\,n \to \mathbb{C}$, and a topological parameter space $P$. Given matrices $M_a(p) \in \mathbb{C}^{R\times R}$ and continuous linear maps $A_{k,a}(p)$ on $\mathbb{C}^R$ (for $a \le d_2$, $k < d$), each continuous in $p$ and with all entries, resp. operator norms, bounded by $L$; a non-zero $q \in \mathbb{C}[X]$ with $q(M_0(p)) = 0$ for every $p$; functions $c_{p,i,j}, c'_{p,i,j} : \mathbb{R} \to \mathbb{C}^R$ ($i < n$, $j < J$) with $(p,z) \mapsto c_{p,i,j}(z)$ continuous on $P \times (0,1]$, such that on $(0,1]$ the function $c_{p,i,j}$ has derivative $c'_{p,i,j}(z)$ and satisfies the folded system $z\,c'_{p,i,j}(z) = \sum_{a \le d_2} \sum_{i' :\, e_{i'}+a = e_i} \big(M_a(p)c_{p,i',j}(z) + \sum_{k<d} z^{k+1} A_{k,a}(p)c_{p,i',j}(z)\big)$; a real $m$ and $B : P \to \mathbb{R}$ locally bounded above with $\|c_{p,i,j}(z)\| \le B(p) z^{-m}$ on $(0,1]$; and reals $\rho_2, \theta$ such that every shift $e'+N$ ($N \in \mathbb{N}$) of a root $e'$ of $q$ with $\mathrm{Re}(e'+N) > \rho_2$ satisfies $\mathrm{Re}(e'+N) > \theta$. Then there are $D \le n \deg q$, a finite set $S$ of such shifted roots with real parts $\le \rho_2$, a constant $\kappa$, and vectors $c^{(2)}_{\mu,j_2}(p,i,j) \in \mathbb{C}^R$, continuous in $p$ and of norm $\le \kappa B(p)$, with $\big\| c_{p,i,j}(z) - \sum_{\mu \in S}\sum_{j_2 < D} z^{\mu}(\log z)^{j_2} c^{(2)}_{\mu,j_2}(p,i,j)\big\| \le \kappa B(p) z^{\theta}$ for all $z \in (0,1]$.
--
--   This is the parameter-dependent Frobenius-type expansion of solutions of a first-order system with a regular singularity at $z = 0$, in the "folded" form where several exponent classes $e_i$ are coupled by shifts $e_{i'} + a = e_i$; the expansion is along the shifted roots of a polynomial annihilating the residue matrix, with uniform constants and coefficients continuous in the parameter. It is obtained from the single-system version [`RegularSingular.exists_logDepth_le_natDegree_norm_sub_expansion_le`](thm.html#RegularSingular.exists_logDepth_le_natDegree_norm_sub_expansion_le), and is used for the two-level expansion [`RegularSingular.exists_twoLevel_expansion_of_commuting_systems`](thm.html#RegularSingular.exists_twoLevel_expansion_of_commuting_systems) and in the cubic-induction analysis of ratio coefficients in the Langlands–Tunnell argument. Note that the conclusion does not assert vanishing of the coefficients with $\mathrm{Re}\,\mu < -m$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_RegularSingular_exists_expansion_coeff_of_folded_system.lean

import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.Topology.Instances.Matrix
import Mathlib.Tactic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem RegularSingular.exists_expansion_coeff_of_folded_system
    {n J R d₂ d : ℕ} (e : Fin n → ℂ) (he : Function.Injective e)
    (P : Type*) [TopologicalSpace P]
    (Mc : P → Fin (d₂ + 1) → Matrix (Fin R) (Fin R) ℂ)
    (A : P → Fin d → Fin (d₂ + 1) → ((Fin R → ℂ) →L[ℂ] (Fin R → ℂ)))
    (L : ℝ) (hMc : ∀ a, Continuous fun p => Mc p a) (hMcL : ∀ p a i j, ‖Mc p a i j‖ ≤ L)
    (hA : ∀ k a, Continuous fun p => A p k a) (hAL : ∀ p k a, ‖A p k a‖ ≤ L)
    (q : Polynomial ℂ) (hq : q ≠ 0) (hann : ∀ p, Polynomial.aeval (Mc p 0) q = 0)
    (c c' : P → Fin n → Fin J → ℝ → (Fin R → ℂ))
    (hcont : ∀ i j, ContinuousOn (fun w : P × ℝ => c w.1 i j w.2) (Set.univ ×ˢ Set.Ioc 0 1))
    (hsys : ∀ p i j, ∀ z ∈ Set.Ioc (0 : ℝ) 1, HasDerivAt (c p i j) (c' p i j z) z ∧
      (z : ℂ) • c' p i j z = ∑ a : Fin (d₂ + 1), ∑ i' : Fin n, if e i' + (a : ℕ) = e i then
        Matrix.mulVec (Mc p a) (c p i' j z) + ∑ k : Fin d, ((z : ℂ) ^ ((k : ℕ) + 1)) • A p k a (c p i' j z)
      else 0)
    (m : ℝ) (B : P → ℝ) (hB : ∀ p₀ : P, ∃ B₀ : ℝ, ∀ᶠ p in nhds p₀, B p ≤ B₀)
    (hbound : ∀ p i j, ∀ z ∈ Set.Ioc (0 : ℝ) 1, ‖c p i j z‖ ≤ B p * z ^ (-m))
    (ρ₂ θ : ℝ) (hθ : ∀ e' : ℂ, q.IsRoot e' → ∀ N : ℕ, ρ₂ < (e' + N).re → θ < (e' + N).re) :
    ∃ (D : ℕ) (S : Finset ℂ) (κ : ℝ), D ≤ n * q.natDegree ∧
      (∀ μ ∈ S, μ.re ≤ ρ₂ ∧ ∃ (e' : ℂ) (N : ℕ), q.IsRoot e' ∧ μ = e' + N) ∧
      ∃ c₂ : ℂ → ℕ → P → Fin n → Fin J → (Fin R → ℂ),
        (∀ μ j₂ i j, Continuous fun p => c₂ μ j₂ p i j) ∧
        ∀ p i j, (∀ μ j₂, ‖c₂ μ j₂ p i j‖ ≤ κ * B p) ∧
          ∀ z ∈ Set.Ioc (0 : ℝ) 1,
            ‖c p i j z - ∑ μ ∈ S, ∑ j₂ ∈ Finset.range D,
                ((z : ℂ) ^ μ * ((Real.log z : ℝ) : ℂ) ^ j₂) • c₂ μ j₂ p i j‖ ≤ κ * B p * z ^ θ := by sorry
