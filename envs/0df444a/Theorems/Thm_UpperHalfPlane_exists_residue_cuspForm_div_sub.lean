-- Prove2me | Theorems.Thm_UpperHalfPlane_exists_residue_cuspForm_div_sub
-- name    : UpperHalfPlane.exists_residue_cuspForm_div_sub
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.683932+00:00
-- url     : https://prove2.me/theorems/29b68d0c-045c-58c2-89af-ab9900eb2442
-- title:
--   Residues of f dτ/(F-t) on X(Γ)
-- statement:
--   Let $\Gamma$ be a finite-index subgroup of $\mathrm{SL}_2(\mathbb{Z})$, let $f$ be a cusp form of weight $2$ for $\Gamma$, and let $F : \mathbb{H} \to \mathbb{C}$ be a function such that, reading $F$ on $\mathbb{C}$ through `UpperHalfPlane.ofComplex`, the function $z \mapsto F(\mathrm{ofComplex}\,z)$ is meromorphic at every point $\tau \in \mathbb{H}$, and such that $F(\gamma \cdot \tau) = F(\tau)$ for all $\gamma \in \Gamma$ and $\tau \in \mathbb{H}$. Fix $t \in \mathbb{C}$ and assume: at every $\tau \in \mathbb{H}$ the meromorphic order of $F - t$ is at most $1$, and for every $\sigma \in \mathrm{SL}_2(\mathbb{Z})$ there is $L \neq t$ with $F(\sigma \cdot \tau) \to L$ as $\mathrm{Im}\,\tau \to \infty$. Then there exists $c : \mathbb{H} \to \mathbb{C}$ such that: (i) for every $\tau \in \mathbb{H}$ there is $g$ analytic at $\tau$ with $f(z)/(F(z) - t) = c(\tau)/(z - \tau) + g(z)$ for all $z \neq \tau$ in a punctured neighbourhood of $\tau$; (ii) $c(\gamma \cdot \tau) = c(\tau)$ for all $\gamma \in \Gamma$; (iii) $c(\tau) \neq 0$ forces the meromorphic order of $F - t$ at $\tau$ to be positive; and (iv) for every finite set $S \subseteq \mathbb{H}$ whose $\Gamma$-orbits cover all points where $c$ is non-zero and whose elements are pairwise $\Gamma$-inequivalent, $\sum_{\sigma \in S} c(\sigma)/\#\mathrm{Stab}_\Gamma(\sigma) = 0$.
--
--   This packages the residue theorem for the meromorphic differential $\omega = f\,d\tau/(F - t)$ on the modular curve $X(\Gamma)$: the differential has at most simple poles, located at the zeros of $F - t$ in $\mathbb{H}$ and none at the cusps, its residues are $\Gamma$-invariant, and their stabiliser-weighted sum over a set of orbit representatives vanishes; the vanishing of the sum is obtained from [`UpperHalfPlane.sum_residue_div_card_stabilizer_eq_zero_of_slashInvariant`](thm.html#UpperHalfPlane.sum_residue_div_card_stabilizer_eq_zero_of_slashInvariant). It is used in the study of fibre sums under the Abel–Jacobi map, in [`ModularCurve.eventually_abelFibreSumOf_sub_mem_periodLatticeOf`](thm.html#ModularCurve.eventually_abelFibreSumOf_sub_mem_periodLatticeOf) and [`ModularCurve.eventually_abelFibreSum_sub_mem_periodLattice`](thm.html#ModularCurve.eventually_abelFibreSum_sub_mem_periodLattice).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_UpperHalfPlane_exists_residue_cuspForm_div_sub.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open UpperHalfPlane
open scoped MatrixGroups Topology

theorem UpperHalfPlane.exists_residue_cuspForm_div_sub
    (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (f : CuspForm Γ 2) (F : ℍ → ℂ)
    (hF : ∀ τ : ℍ, MeromorphicAt (fun z : ℂ => F (ofComplex z)) (τ : ℂ))
    (hΓ : ∀ γ ∈ Γ, ∀ τ : ℍ, F (γ • τ) = F τ) (t : ℂ)
    (hsimple : ∀ τ : ℍ, meromorphicOrderAt (fun z : ℂ => F (ofComplex z) - t) (τ : ℂ) ≤ 1)
    (hcusp : ∀ σ : SL(2, ℤ), ∃ L : ℂ, L ≠ t ∧
      Filter.Tendsto (fun τ : ℍ => F (σ • τ)) atImInfty (𝓝 L)) :
    ∃ c : ℍ → ℂ,
      (∀ τ : ℍ, ∃ g : ℂ → ℂ, AnalyticAt ℂ g (τ : ℂ) ∧
        ∀ᶠ z in 𝓝[≠] (τ : ℂ),
          f (ofComplex z) / (F (ofComplex z) - t) = c τ / (z - τ) + g z) ∧
      (∀ γ ∈ Γ, ∀ τ : ℍ, c (γ • τ) = c τ) ∧
      (∀ τ : ℍ, c τ ≠ 0 →
        0 < meromorphicOrderAt (fun z : ℂ => F (ofComplex z) - t) (τ : ℂ)) ∧
      ∀ S : Finset ℍ, (∀ τ : ℍ, c τ ≠ 0 → ∃ σ ∈ S, ∃ γ ∈ Γ, γ • σ = τ) →
        (∀ σ ∈ S, ∀ σ' ∈ S, ∀ γ ∈ Γ, γ • σ = σ' → σ = σ') →
        ∑ σ ∈ S, c σ / Nat.card (MulAction.stabilizer Γ σ) = 0 := by sorry
