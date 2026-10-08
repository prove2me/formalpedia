-- Prove2me | Theorems.Thm_QuantumWalkSearch_ApproxRAA_lemma_1
-- name    : QuantumWalkSearch.ApproxRAA.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T08:42:51.329+00:00
-- url     : https://prove2.me/theorems/4ea722e3-9269-4fc6-adf7-2575d59ac815
-- title:
--   Lemma 1 — with t the first hit of sin⁻¹√p_M, Approximate RAA(t, γ) leaves a projection of length ≥ 1/√2 − γ on the marked subspace
-- statement:
--   Let $|\pi\rangle\in\mathcal H=\mathbb C^{X\times X}$ be a unit vector, $M\subseteq X$ a marked set, $p_M=\|\Pi_M|\pi\rangle\|^2$ and $\gamma>0$. For $i\ge1$ let $R_i$ be a unitary on $\mathcal H\otimes K_i$ with
--
--   1. $R_i|\pi\rangle|0\rangle=|\pi\rangle|0\rangle$, and
--   2. $\|(R_i+\mathrm{Id})|\psi\rangle|0\rangle\|\le\beta_i\|\psi\|$ for every $|\psi\rangle\perp|\pi\rangle$, where $\beta_i=\frac{18}{4\pi^3}\frac{\gamma}{i^2}$.
--
--   Let $t$ be the smallest non-negative integer such that $3^t\sin^{-1}\sqrt{p_M}\in[\pi/4,3\pi/4]$. Then Approximate RAA$(t,\gamma)$ maps $|\pi\rangle|0^S\rangle$ to a state whose projection on the marked subspace $\mathcal M\otimes[\bigotimes_{i=1}^tK_i]$ has length at least $1/\sqrt2-\gamma$:
--   $$
--   \big\|\Pi_{\tilde M}\,A_t\,|\pi\rangle|0^S\rangle\big\|\ \ge\ \frac1{\sqrt2}-\gamma .
--   $$
--
--   This is the version of recursive amplitude amplification in which the reflection about the initial state is only available approximately, with errors that shrink like $\gamma/i^2$ across levels; the total error stays of order $\gamma$.
--
--   **Formalization Note** The cost clause of the paper ("incurs a cost of order $3^t(c_1\log1/\gamma+c_2)$") is not formalized, nor is property 1 of $R(\beta)$. The circuits are required only at the precisions $\beta_1,\beta_2,\dots$, which makes the hypothesis weaker than the paper's "for any $\beta>0$". The existence of $t$ forces $p_M>0$. The extended space has exactly the $t$ registers $K_1,\dots,K_t$.
-- source:
--   Magniez, Nayak, Roland, Santha, Search via Quantum Walk, arXiv:quant-ph/0608026v4, p. 12, Lemma 1 (proof pp. 12–15)

import Mathlib
import Definitions.Def_QuantumWalkSearch_ApproxRAA_Setting
import Definitions.Def_QuantumWalkSearch_ApproxRAA_Circuit

namespace QuantumWalkSearch.ApproxRAA

/-- Lemma 1 (p. 12), exact half. Let `t` be the smallest non-negative integer with
`3^t sin⁻¹ √p_M ∈ [π/4, 3π/4]`. For every `γ > 0`, if the circuits `R i` satisfy properties
2–3 at `β_i = 18γ/(4π³ i²)`, then Approximate RAA(t, γ), on `H ⊗ [⊗_{i=1}^{t} K_i]`, maps
`|π⟩|0^S⟩` to a state whose projection on `M ⊗ [⊗_{i=1}^{t} K_i]` has length at least
`1/√2 − γ`. (The cost clause is not formalized.) -/
theorem lemma_1 {X : Type*} [Fintype X] [DecidableEq X] {κ : ℕ → Type*}
    [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)]
    (M : Finset X) (piState : EuclideanSpace ℂ (X × X)) (hπ : ‖piState‖ = 1)
    (z : ∀ i, κ i) (R : ∀ i, Matrix (X × X × κ i) (X × X × κ i) ℂ) (γ : ℝ) (hγ : 0 < γ)
    (hR : ApproxReflections piState z R γ) (t : ℕ)
    (ht : IsFirstHit (Real.arcsin (Real.sqrt (markedWeight M piState))) t) :
    1 / Real.sqrt 2 - γ ≤ ‖act (markedProj M) (phi M z R piState t t)‖ := by sorry

end QuantumWalkSearch.ApproxRAA
