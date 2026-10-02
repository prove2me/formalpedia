-- Prove2me | Theorems.Thm_TeschlQM_OneParticle_schroedinger_selfAdjoint
-- name    : TeschlQM.OneParticle.schroedinger_selfAdjoint
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-29T08:07:05.368087+00:00
-- url     : https://prove2.me/theorems/6aab96ea-8595-4941-a4cb-9b4d8882a7c4
-- title:
--   Theorem 10.2 — H₀ + V is self-adjoint on H²(ℝⁿ), bounded below, σ_ess = [0, ∞), C_c^∞ core
-- statement:
--   Let $n \ge 1$ and let $V : \mathbb R^n \to \mathbb R$ satisfy $V \in L^\infty_\infty(\mathbb R^n)$ if $n > 3$, and $V \in L^\infty_\infty(\mathbb R^n) + L^2(\mathbb R^n)$ if $n \le 3$, where $L^\infty_\infty$ are the bounded Borel functions vanishing at infinity. Then the multiplication operator $V$ is relatively compact with respect to $H_0 = -\Delta$. In particular,
--   $$H = H_0 + V, \qquad \mathfrak D(H) = H^2(\mathbb R^n),$$
--   is self-adjoint and bounded from below,
--   $$\sigma_{ess}(H) = [0, \infty),$$
--   and $C_c^\infty(\mathbb R^n)$ is a core for $H$.
--
--   This is the basic existence theorem for one-particle Schrödinger operators with decaying potentials, including the Coulomb potential in three dimensions: the Hamiltonian is a well-defined observable, its energy is bounded below, and all spectrum below zero consists of isolated eigenvalues of finite multiplicity.
--
--   **Formalization Note.** $V$ is the maximally defined multiplication operator `multOp`, and $H_0 + V$ is the `LinearPMap` sum with domain $\mathfrak D(H_0) \cap \mathfrak D(V)$; that this domain equals $H^2(\mathbb R^n)$ is a conclusion. "$V \in L^\infty_\infty + L^2$" is $V = V_1 + V_2$ pointwise with $V_1$ bounded, Borel and vanishing at infinity and $V_2 \in L^2$. The only hypotheses are these function-space conditions: neither $\mathfrak D(H_0) \subseteq \mathfrak D(V)$ nor a relative bound is assumed. Self-adjointness is Mathlib's `IsSelfAdjoint`, $[0,\infty)$ is the image of `Set.Ici 0` in $\mathbb C$, and "core" is Mathlib's `LinearPMap.HasCore` (the closure of $H$ restricted to $C_c^\infty$ is $H$). The Fourier normalization is Mathlib's; $H_0$ and $H^2$ do not depend on it. $n \ge 1$ excludes the zero-dimensional space, where $\sigma_{ess}$ is empty.
-- source:
--   Teschl, Mathematical Methods in Quantum Mechanics, AMS GSM 99, 2009, p. 222, Theorem 10.2

import Mathlib
import Definitions.Def_TeschlQM_OneParticle_multiplicationOperator
import Definitions.Def_TeschlQM_OneParticle_freeHamiltonian
import Definitions.Def_TeschlQM_Shared_resolventSet
import Definitions.Def_TeschlQM_OneParticle_essentialSpectrum
import Definitions.Def_TeschlQM_Shared_IsRelativelyCompact
import Definitions.Def_TeschlQM_OneParticle_IsBoundedBelow
import Definitions.Def_TeschlQM_OneParticle_testFunctions
import Definitions.Def_TeschlQM_OneParticle_IsBoundedVanishingAtInfinity

namespace TeschlQM.OneParticle

open MeasureTheory

/-- Teschl, Theorem 10.2, p. 222. Let `V` be real-valued and `V ∈ L^∞_∞(ℝⁿ)` if `n > 3` and
`V ∈ L^∞_∞(ℝⁿ) + L²(ℝⁿ)` if `n ≤ 3`. Then `V` is relatively compact with respect to `H₀`. In
particular, `H = H₀ + V`, `𝔇(H) = H²(ℝⁿ)` (10.3), is self-adjoint, bounded from below and
`σ_ess(H) = [0, ∞)` (10.4). Moreover, `C_c^∞(ℝⁿ)` is a core for `H`.

`V` is the maximally defined multiplication operator (2.21) and `H₀ + V` is the operator sum on
`𝔇(H₀) ∩ 𝔇(V)`; that this intersection is `H²(ℝⁿ)` is part of the conclusion. `n ≥ 1` (the book's
`ℝⁿ` is at least one-dimensional; on `ℝ⁰` the essential spectrum is empty). -/
theorem schroedinger_selfAdjoint (n : ℕ) (hn : 1 ≤ n) (V : EuclideanSpace ℝ (Fin n) → ℝ)
    (hV_large : 3 < n → IsBoundedVanishingAtInfinity V)
    (hV_small : n ≤ 3 → ∃ V₁ V₂ : EuclideanSpace ℝ (Fin n) → ℝ,
      IsBoundedVanishingAtInfinity V₁ ∧ MemLp V₂ 2 volume ∧ V = V₁ + V₂) :
    TeschlQM.Shared.IsRelativelyCompact (multOp (fun x => (V x : ℂ))) (freeHamiltonian n) ∧
      (freeHamiltonian n + multOp (fun x => (V x : ℂ))).domain = sobolevH2 n ∧
      IsSelfAdjoint (freeHamiltonian n + multOp (fun x => (V x : ℂ))) ∧
      IsBoundedBelow (freeHamiltonian n + multOp (fun x => (V x : ℂ))) ∧
      essentialSpectrum (freeHamiltonian n + multOp (fun x => (V x : ℂ))) =
        (fun t : ℝ => (t : ℂ)) '' Set.Ici 0 ∧
      (freeHamiltonian n + multOp (fun x => (V x : ℂ))).HasCore (testFunctions n) := by sorry

end TeschlQM.OneParticle
