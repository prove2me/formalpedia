-- Prove2me | Theorems.Thm_RandKSATSample_Main_lemma_4_4
-- name    : RandKSATSample.Main.lemma_4_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T02:59:04.076025+00:00
-- url     : https://prove2.me/theorems/66f1eb4f-3c45-44ba-935a-aa2faeb3aced
-- title:
--   Lemma 4.4 — component-swap variance comparison: Var_π(f) ≤ (max_j E_ζ[2^{|A_j|} e^{R(A_j)}]) Σ_j V_j^π(f) for the finite-interaction measure (4.26)
-- statement:
--   Let $s\ge1$, $\Omega_1,\dots,\Omega_s$ nonempty finite sets, $\Omega=\prod_i\Omega_i$, local weights $\ell_i:\Omega_i\to(0,\infty)$, a finite set $\mathcal J$ of labelled hyperedges with nonempty vertex sets $V_e\subseteq[s]$, coefficients $a_e\in\mathbb R$ and indicators $Y_e$ of $\sigma_{V_e}$. The measure $\pi$ of (4.26) is well defined and strictly positive. Let $\zeta$ keep each $e$ independently with probability $1-e^{-2|a_e|}$ (4.28), $A_j$ the vertex set of the component of $\zeta$ containing $j$, and $R(A)=\sum_{e:V_e\cap A\ne\emptyset}|a_e|$ (4.27). Then for every $f:\Omega\to\mathbb R$,
--   $$\mathrm{Var}_\pi(f)\le\Big(\max_{j\in[s]}\mathbb E_\zeta\big[2^{|A_j|}e^{R(A_j)}\big]\Big)\sum_{j=1}^sV_j^\pi(f)\quad(4.29).$$
--   It is the variance tensorization step from which the spectral gap of the core heat bath follows.
--
--   Differences from the source:
--   - encoding: Y_e : ∏_{i∈V_e} Ω_i → {0,1} → Y e : Ω → Bool with hypothesis hY: Y e depends only on σ_{V_e}; reason: the same functions
--   - encoding: "well defined and strictly positive" (π a probability measure) → conclusions ∀ σ, 0 < π σ and Σ_σ π σ = 1; reason: the printed claim, stated explicitly
-- source:
--   He, Li, Yang, Fast Almost-Uniform Sampling of Random k-SAT Solutions, arXiv:2610.10474 (version not printed; file sha256 563a4d84…), pp. 26–27, Lemma 4.4

import Mathlib
import Definitions.Def_RandKSATSample_Main_FiniteInteraction

set_option autoImplicit false

open Classical

namespace RandKSATSample.Main

/-- Lemma 4.4 (component-swap variance comparison): for the finite-interaction measure `π` of
(4.26) on `Ω = Π_{i ∈ [s]} Ω_i` (well defined and strictly positive), and the random labelled
hypergraph `ζ` with independent edges `P(ζ_e = 1) = 1 − e^{−2|a_e|}` (4.28), every
`f : Ω → ℝ` satisfies `Var_π(f) ≤ (max_j E_ζ[2^{|A_j|} e^{R(A_j)}]) Σ_j V_j^π(f)` (4.29). -/
theorem lemma_4_4 (s : ℕ) (hs : 0 < s) (Ωi : Fin s → Type) [∀ i, Fintype (Ωi i)]
    [∀ i, Nonempty (Ωi i)] (lw : ∀ i, Ωi i → ℝ) (hlw : ∀ i x, 0 < lw i x)
    (J : Type) [Fintype J] (V : J → Finset (Fin s)) (hV : ∀ e, (V e).Nonempty)
    (a : J → ℝ) (Y : J → (∀ i, Ωi i) → Bool)
    (hY : ∀ e σ σ', (∀ i ∈ V e, σ i = σ' i) → Y e σ = Y e σ') :
    (∀ σ, 0 < interactionMeasure lw a Y σ) ∧ ∑ σ, interactionMeasure lw a Y σ = 1 ∧
    ∀ f : (∀ i, Ωi i) → ℝ,
      variance (interactionMeasure lw a Y) f ≤
        (Finset.univ.sup' ⟨⟨0, hs⟩, Finset.mem_univ _⟩ fun j => hyperMoment V a j) *
          ∑ j, condVarAvg (interactionMeasure lw a Y) f (AgreeExcept j) := by sorry

end RandKSATSample.Main
