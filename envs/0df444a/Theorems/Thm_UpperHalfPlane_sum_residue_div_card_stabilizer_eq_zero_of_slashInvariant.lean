-- Prove2me | Theorems.Thm_UpperHalfPlane_sum_residue_div_card_stabilizer_eq_zero_of_slashInvariant
-- name    : UpperHalfPlane.sum_residue_div_card_stabilizer_eq_zero_of_slashInvariant
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.683932+00:00
-- url     : https://prove2.me/theorems/79655372-fb65-5d3b-b4dd-00864bbd06f8
-- title:
--   Vanishing of stabiliser-weighted residue sums for weight-2 invariants
-- statement:
--   Let $\Gamma$ be a subgroup of finite index in $\mathrm{SL}_2(\mathbb{Z})$, let $\omega, c : \mathfrak{H} \to \mathbb{C}$ be functions on the upper half plane and let $S$ be a finite subset of $\mathfrak{H}$. Assume: (1) $\omega \mid_2 \gamma = \omega$ for every $\gamma \in \Gamma$, for the weight-$2$ slash action; (2) for every $\sigma \in \mathrm{SL}_2(\mathbb{Z})$ there is a $\delta > 0$ with $\omega \mid_2 \sigma = O\!\left(e^{-\delta \operatorname{Im} \tau}\right)$ along the filter `atImInfty` of points of large imaginary part; (3) for every $\tau \in \mathfrak{H}$ there is a function $g : \mathbb{C} \to \mathbb{C}$, analytic at the point $\tau$ of $\mathbb{C}$, such that $\omega(z) = c(\tau)/(z - \tau) + g(z)$ for all $z$ in a punctured neighbourhood of $\tau$, the value of $\omega$ at $z$ being taken through the section `ofComplex` of the inclusion $\mathfrak{H} \hookrightarrow \mathbb{C}$; (4) every $\tau$ with $c(\tau) \neq 0$ is of the form $\gamma \cdot \sigma$ for some $\sigma \in S$ and $\gamma \in \Gamma$; and (5) if $\sigma, \sigma' \in S$ and $\gamma \cdot \sigma = \sigma'$ for some $\gamma \in \Gamma$, then $\sigma = \sigma'$. The conclusion is $\sum_{\sigma \in S} c(\sigma) / \#\mathrm{Stab}_\Gamma(\sigma) = 0$, the cardinality being that of the stabiliser of $\sigma$ in $\Gamma$ for the action on $\mathfrak{H}$.
--
--   This is the residue theorem for the modular curve $X(\Gamma) = \Gamma \backslash \mathfrak{H}^{*}$, read on the upper half plane: conditions (1)–(3) say that $\omega(\tau)\,d\tau$ descends to a meromorphic differential with at most simple poles and with exponential decay at every cusp, and the conclusion is the vanishing of the sum of its residues, each residue at $\tau$ being divided by the order of the stabiliser to account for the ramification of $\mathfrak{H} \to X(\Gamma)$. It is deduced from the level-one case [`UpperHalfPlane.levelOne_sum_residue_div_card_stabilizer_eq_zero`](thm.html#UpperHalfPlane.levelOne_sum_residue_div_card_stabilizer_eq_zero), and is used in the analysis of divisors and orders of vanishing of modular functions on $X(\Gamma)$, in particular for $\Gamma_H$-level curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_UpperHalfPlane_sum_residue_div_card_stabilizer_eq_zero_of_slashInvariant.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open UpperHalfPlane
open scoped MatrixGroups Topology ModularForm

theorem UpperHalfPlane.sum_residue_div_card_stabilizer_eq_zero_of_slashInvariant
    (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (ω : ℍ → ℂ) (c : ℍ → ℂ) (S : Finset ℍ)
    (hΓ : ∀ γ ∈ Γ, ω ∣[(2 : ℤ)] γ = ω)
    (hcusp : ∀ σ : SL(2, ℤ), ∃ δ : ℝ, 0 < δ ∧
        (ω ∣[(2 : ℤ)] σ) =O[atImInfty] fun τ : ℍ => Real.exp (-δ * τ.im))
    (hloc : ∀ τ : ℍ, ∃ g : ℂ → ℂ, AnalyticAt ℂ g (τ : ℂ) ∧
        ∀ᶠ z in 𝓝[≠] (τ : ℂ), ω (ofComplex z) = c τ / (z - τ) + g z)
    (hS : ∀ τ : ℍ, c τ ≠ 0 → ∃ σ ∈ S, ∃ γ ∈ Γ, γ • σ = τ)
    (hinj : ∀ σ ∈ S, ∀ σ' ∈ S, ∀ γ ∈ Γ, γ • σ = σ' → σ = σ') :
    ∑ σ ∈ S, c σ / Nat.card (MulAction.stabilizer Γ σ) = 0 := by sorry
