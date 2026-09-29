-- Prove2me | Theorems.Thm_UpperHalfPlane_eventually_forall_exists_smul_mem_of_meromorphicOrderAt_pos
-- name    : UpperHalfPlane.eventually_forall_exists_smul_mem_of_meromorphicOrderAt_pos
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.683932+00:00
-- url     : https://prove2.me/theorems/57d8e2d2-cf40-5e96-b039-fcb2172e15ac
-- title:
--   Fibres of F near a non-cuspidal value stay in Γ U
-- statement:
--   Let $\Gamma$ be a finite-index subgroup of $\mathrm{SL}(2,\mathbb Z)$ and let $F : \mathbb H \to \mathbb C$ be a function on the upper half-plane. Assume: (i) for every $\tau \in \mathbb H$ the function $z \mapsto F(\mathrm{ofComplex}\, z)$ on $\mathbb C$, obtained by reading $F$ through the retraction `UpperHalfPlane.ofComplex`, is meromorphic at the point $\tau$; (ii) $F(\gamma \cdot \tau) = F(\tau)$ for all $\gamma \in \Gamma$ and all $\tau \in \mathbb H$; (iii) a point $t_0 \in \mathbb C$ is given such that for every $\sigma \in \mathrm{SL}(2,\mathbb Z)$ the function $\tau \mapsto F(\sigma \cdot \tau)$ converges along the filter `atImInfty` to some limit $L \ne t_0$. Let $U \subseteq \mathbb H$ be open and suppose that every $\tau \in \mathbb H$ at which $z \mapsto F(\mathrm{ofComplex}\, z) - t_0$ has strictly positive meromorphic order admits some $\gamma \in \Gamma$ with $\gamma \cdot \tau \in U$. The conclusion is that this last property holds for all $t$ in some neighbourhood of $t_0$: eventually in the filter $\mathcal N(t_0)$, every $\tau \in \mathbb H$ with $\mathrm{ord}_\tau(F - t) > 0$ has a $\Gamma$-translate lying in $U$.
--
--   This is the upper semicontinuity, in the parameter $t$, of the condition that the fibre $F^{-1}(t)$ be contained in $\Gamma U$, for a $\Gamma$-invariant meromorphic function whose cusp values avoid $t_0$; geometrically $F$ descends to the compact modular curve $X(\Gamma)$ and the fibre over $t_0$ is a compact set avoiding the cusps. It is used in the construction of Abel–Jacobi type sums over fibres, where the fibre must be kept inside a fixed open set as the base point moves, in [`ModularCurve.eventually_abelFibreSumOf_sub_mem_periodLatticeOf`](thm.html#ModularCurve.eventually_abelFibreSumOf_sub_mem_periodLatticeOf) and [`ModularCurve.eventually_abelFibreSum_sub_mem_periodLattice`](thm.html#ModularCurve.eventually_abelFibreSum_sub_mem_periodLattice).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_UpperHalfPlane_eventually_forall_exists_smul_mem_of_meromorphicOrderAt_pos.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open UpperHalfPlane
open scoped MatrixGroups Topology

theorem UpperHalfPlane.eventually_forall_exists_smul_mem_of_meromorphicOrderAt_pos
    (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (F : ℍ → ℂ)
    (hF : ∀ τ : ℍ, MeromorphicAt (fun z : ℂ => F (ofComplex z)) (τ : ℂ))
    (hΓ : ∀ γ ∈ Γ, ∀ τ : ℍ, F (γ • τ) = F τ) (t₀ : ℂ)
    (hcusp : ∀ σ : SL(2, ℤ), ∃ L : ℂ, L ≠ t₀ ∧
      Filter.Tendsto (fun τ : ℍ => F (σ • τ)) atImInfty (𝓝 L))
    {U : Set ℍ} (hU : IsOpen U)
    (hfib : ∀ τ : ℍ, 0 < meromorphicOrderAt (fun z : ℂ => F (ofComplex z) - t₀) (τ : ℂ) →
      ∃ γ ∈ Γ, γ • τ ∈ U) :
    ∀ᶠ t in 𝓝 t₀, ∀ τ : ℍ,
      0 < meromorphicOrderAt (fun z : ℂ => F (ofComplex z) - t) (τ : ℂ) →
        ∃ γ ∈ Γ, γ • τ ∈ U := by sorry
