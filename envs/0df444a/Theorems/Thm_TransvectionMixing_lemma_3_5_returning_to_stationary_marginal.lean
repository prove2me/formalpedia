-- Prove2me | Theorems.Thm_TransvectionMixing_lemma_3_5_returning_to_stationary_marginal
-- name    : TransvectionMixing.lemma_3_5_returning_to_stationary_marginal
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:20:45.567865+00:00
-- url     : https://prove2.me/theorems/0fb38d4e-2f3f-4c62-9a7b-f770b53e7e00
-- title:
--   Lemma 3.5 — returning to the stationary marginal
-- statement:
--   Let $n\ge 2$, $\mathcal S\subseteq[n]\times[n]$, and let $\nu$ be a law on the requested entries $\mathbb F_q^{\mathcal S}$. Let $\delta\ge 0$ and $\rho\in\mathbb R$. Suppose that, for every initial state $X\in\mathrm{SL}_n(\mathbb F_q)$, a uniformly random skeleton of length $T$ satisfies
--   $$
--   \Pr_\sigma\bigl[\|K_{\sigma,\mathcal S}(X,\cdot)-\nu\|_{TV}>\delta\bigr]\le\rho .
--   $$
--   Then
--   $$
--   \|\pi_{\mathcal S}-\nu\|_{TV}\le\rho+\delta,\qquad d_{\mathcal S}(T)\le 2(\rho+\delta),\qquad \sup_X\Pr_\sigma\bigl[d^\sigma_{\mathcal S}(X)>\rho+2\delta\bigr]\le\rho .
--   $$
--
--   It transfers a bound against a reference law (such as the product-uniform law) to both guarantees against the stationary marginal $\pi_{\mathcal S}$.
--
--   Differences from the source:
--   - reading: δ, a total-variation tolerance (sign unstated) → hypothesis 0 ≤ δ; reason: for δ < 0 the hypothesis forces ρ ≥ 1 and the first conclusion can fail; a TV threshold is nonnegative in every use (δ = u/8 ≥ 0)
--   - encoding: the walk on n rows (the paper's results take n ≥ 2 implicitly: a step needs two distinct rows) → hypothesis 2 ≤ n; reason: excludes only n ≤ 1, where no skeleton of positive length exists
--   - encoding: laws of the walk over uniform skeletons and uniform coefficients → normalized counts (`prob`, `skelLaw`, `entryLaw`, `piS`) over finite types; reason: Lean convention for finite uniform probability; same values
--   - encoding: ‖·‖_TV → the published `MarkovMixing.tvDist` (max over events of |μ(A) − ν(A)|); reason: equals ½∑|μ − ν| on probability vectors; same values
-- source:
--   Braverman, Jain, Newman, Optimal Marginal Mixing for Transvection-Based Trapdoored Matrices over Large Fields (manuscript, sha256 217f833f…), Lemma 3.5, p.12

import Mathlib
import Definitions.Def_mm_basic
import Definitions.Def_mm_mixing
import Definitions.Def_TransvectionMixing_dS

namespace TransvectionMixing

/-- **Lemma 3.5** (returning to the stationary marginal) (Braverman–Jain–Newman, *Optimal Marginal Mixing for Transvection-Based Trapdoored Matrices over
Large Fields*, manuscript sha256 217f833f…, §3.3, p.12). Let `ν` be a law
on the requested entries `𝒮`. Suppose that, for every initial state `X ∈ SLₙ(𝔽_q)`, a random
length-`T` skeleton satisfies `Pr_σ[‖K_{σ,𝒮}(X, ·) − ν‖_TV > δ] ≤ ρ`. Then
`‖π_𝒮 − ν‖_TV ≤ ρ + δ`, `d_𝒮(T) ≤ 2(ρ + δ)`, and `sup_X Pr_σ[d^σ_𝒮(X) > ρ + 2δ] ≤ ρ`.

**Formalization Note** `n ≥ 2` (the walk needs two distinct rows) and `δ ≥ 0` (a total
variation tolerance) are stated explicitly. -/
theorem lemma_3_5_returning_to_stationary_marginal (F : Type*) [Field F] [Fintype F]
    [DecidableEq F] (n : ℕ) (hn : 2 ≤ n) (S : Finset (Fin n × Fin n)) (T : ℕ)
    (ν : (↥S → F) → ℝ) (hν : MarkovMixing.IsDist ν) (δ ρ : ℝ) (hδ : 0 ≤ δ)
    (h : ∀ X : Matrix.SpecialLinearGroup (Fin n) F,
      prob (fun σ : Skel n T => δ < MarkovMixing.tvDist (skelLaw F σ X S) ν) ≤ ρ) :
    MarkovMixing.tvDist (piS F S) ν ≤ ρ + δ ∧ dS F S T ≤ 2 * (ρ + δ) ∧
      (⨆ X : Matrix.SpecialLinearGroup (Fin n) F, skelBadProb F S T X (ρ + 2 * δ))
        ≤ ρ := by sorry

end TransvectionMixing
