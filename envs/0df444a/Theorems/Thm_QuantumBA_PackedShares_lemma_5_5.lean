-- Prove2me | Theorems.Thm_QuantumBA_PackedShares_lemma_5_5
-- name    : QuantumBA.PackedShares.lemma_5_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T07:10:52.619581+00:00
-- url     : https://prove2.me/theorems/7da27c55-aca9-49ce-b0ec-1825cc391625
-- title:
--   Lemma 5.5 — the sharing scheme of QBA:PackedShares provides fresh common coins
-- statement:
--   Consider QBA:PackedShares with symbolic parameters satisfying the standing assumptions. Suppose that every forwarding graph has properties (i)–(iii) of Lemma 5.3 for sampler error $\rho$, that
--   $$\gamma+2\rho+D_\ell^{-1}<\theta\quad\text{and}\quad p_\ell+3\sigma(D_\ell)\le D_\ell$$
--   for every level $\ell$ with transfers, and that $(\gamma+\rho)k_1\le\sigma(k_1)$ unless the level-1 committees are $P$. Then the sharing scheme of QBA:PackedShares provides fresh common coins in the sense of Definition 3.2, up to the first honest decision in epochs entered before it, with the committee budgets $\mathrm{Bud}_v$.
--
--   This connects the quantum implementation to the classical election analysis of Section 4.
--
--   Differences from the source:
--   - encoding: the parameters remain symbolic until Section 6 (b, w, h, committees, forwarding graphs, capacities) → the statement holds for every parameter record X : Ctx satisfying the standing assumptions WellFormed X of §1.1, §3.1, §5.1–§5.2; reason: the standing assumptions of the sections are written as one predicate; nothing beyond them is assumed
--   - encoding: latent values S_ω with ρ_{S_{W′}E|h} = q^{-|W′|} Σ_s |s⟩⟨s| ⊗ ρ_{E|h} and reconstruction to S_ω → a family Λ h s of positive operators on the adversary’s registers, summing to the unnormalized adversary state at h and consistent in trace along histories, with the marginal identity on unopened words and Λ h s = 0 whenever a reconstruction by an honest requester returned a value ≠ s_ω; reason: this is the joint classical–quantum law of the latent values, the history and the adversary’s system
-- source:
--   Jan Olkowski, Fast Quantum Byzantine Agreement with Nearly Linear Quantum Communication, STOC 2027 submission #558 (October 2026), source.pdf SHA-256 612d0471810a0aa053891a77995d579d836cc301efd01df8e75c2bbe8ebb5383, p. 30, Lemma 5.5 (PDF p. 31)

import Mathlib
import Definitions.Def_QuantumBA_PackedShares_Analysis

namespace QuantumBA.PackedShares

open scoped BigOperators ENNReal Matrix

/-- Lemma 5.5 (the sharing scheme of QBA:PackedShares provides fresh common coins). -/
theorem lemma_5_5 {n : ℕ} {F : Type} [Field F] [Fintype F] [DecidableEq F] (X : Ctx n F)
    (hX : WellFormed X) (ρ : ℝ)
    (hgraphs : ∀ ℓ, hasTransfer X ℓ → ∀ i < X.m ℓ, FwdGraphProps X ρ ℓ i)
    (hslack : ∀ ℓ, hasTransfer X ℓ → gam X + 2 * ρ + 1 / (X.D ℓ : ℝ) < 1 / 3 - X.ε / 4)
    (hdec : ∀ ℓ, hasTransfer X ℓ → X.p ℓ + 3 * X.sigma (X.D ℓ) ≤ X.D ℓ)
    (hk1 : 1 ≤ X.h → X.k 1 < n → (gam X + ρ) * X.k 1 ≤ X.sigma (X.k 1)) :
    FreshCoins X := by sorry

end QuantumBA.PackedShares
