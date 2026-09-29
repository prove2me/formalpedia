-- Prove2me | Theorems.Thm_UpperHalfPlane_levelOne_sum_residue_div_card_stabilizer_eq_zero
-- name    : UpperHalfPlane.levelOne_sum_residue_div_card_stabilizer_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.683932+00:00
-- url     : https://prove2.me/theorems/1e67913a-a015-561e-827c-8554a7769bcf
-- title:
--   Residue theorem on X(1): weighted residues sum to zero
-- statement:
--   Let $\omega,c:\mathfrak H\to\mathbb C$ be functions on the upper half plane and let $S$ be a finite subset of $\mathfrak H$. Assume: (i) $\omega$ is invariant under the weight-$2$ slash action of the full modular group, $\omega\mid[2]\gamma=\omega$ for every $\gamma\in\mathrm{SL}_2(\mathbb Z)$; (ii) there is a real $\delta>0$ with $\omega(\tau)=O\!\left(e^{-\delta\,\mathrm{Im}\,\tau}\right)$ along the filter `atImInfty`; (iii) for every $\tau\in\mathfrak H$ there is a function $g:\mathbb C\to\mathbb C$, analytic at $\tau$, such that $\omega(z)=c(\tau)/(z-\tau)+g(z)$ for all $z$ in a punctured neighbourhood of $\tau$ (so $\omega$ has at worst a simple pole at $\tau$ with residue $c(\tau)$, the value of $\omega$ at a point of $\mathbb C$ being read off through `ofComplex`); (iv) every $\tau$ with $c(\tau)\neq 0$ is of the form $\gamma\cdot\sigma$ for some $\sigma\in S$ and some $\gamma\in\mathrm{SL}_2(\mathbb Z)$; and (v) if $\sigma,\sigma'\in S$ and $\gamma\cdot\sigma=\sigma'$ for some $\gamma\in\mathrm{SL}_2(\mathbb Z)$, then $\sigma=\sigma'$. Then $$\sum_{\sigma\in S}\frac{c(\sigma)}{\#\,\mathrm{Stab}_{\mathrm{SL}_2(\mathbb Z)}(\sigma)}=0,$$ the stabiliser cardinalities being taken as natural numbers cast into $\mathbb C$.
--
--   This is the residue theorem for a meromorphic weight-two differential on the compactified modular curve $X(1)$, transcribed as a statement about an $\mathrm{SL}_2(\mathbb Z)$-invariant function on $\mathfrak H$ with at most simple poles and exponential decay at the cusp; the division by the order of the stabiliser accounts for the elliptic points $i$ and $\rho$. It is proved from a distributional residue formula for functions with simple poles, the local integrability of such functions, and the vanishing of a suitably cut-off integral of a periodic function decaying at $i\infty$, and it is used to derive the corresponding statement for weight-two slash-invariant functions in [`UpperHalfPlane.sum_residue_div_card_stabilizer_eq_zero_of_slashInvariant`](thm.html#UpperHalfPlane.sum_residue_div_card_stabilizer_eq_zero_of_slashInvariant).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_UpperHalfPlane_levelOne_sum_residue_div_card_stabilizer_eq_zero.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open UpperHalfPlane
open scoped MatrixGroups Topology ModularForm

theorem UpperHalfPlane.levelOne_sum_residue_div_card_stabilizer_eq_zero
    (ω : ℍ → ℂ) (c : ℍ → ℂ) (S : Finset ℍ)
    (hΓ : ∀ γ : SL(2, ℤ), ω ∣[(2 : ℤ)] γ = ω)
    (hcusp : ∃ δ : ℝ, 0 < δ ∧ ω =O[atImInfty] fun τ : ℍ => Real.exp (-δ * τ.im))
    (hloc : ∀ τ : ℍ, ∃ g : ℂ → ℂ, AnalyticAt ℂ g (τ : ℂ) ∧
        ∀ᶠ z in 𝓝[≠] (τ : ℂ), ω (ofComplex z) = c τ / (z - τ) + g z)
    (hS : ∀ τ : ℍ, c τ ≠ 0 → ∃ σ ∈ S, ∃ γ : SL(2, ℤ), γ • σ = τ)
    (hinj : ∀ σ ∈ S, ∀ σ' ∈ S, ∀ γ : SL(2, ℤ), γ • σ = σ' → σ = σ') :
    ∑ σ ∈ S, c σ / Nat.card (MulAction.stabilizer SL(2, ℤ) σ) = 0 := by sorry
