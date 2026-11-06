-- Prove2me | Theorems.Thm_SpinGirth5_potts_local_spectral_contraction
-- name    : SpinGirth5.potts_local_spectral_contraction
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:13:12.629978+00:00
-- url     : https://prove2.me/theorems/5d4c8171-d3cc-4fc5-8982-9dc9c16a388e
-- title:
--   §6 — the Potts model with $q\ge(1+\delta)(1-\beta)\Delta$, $\Delta\ge\delta^{-2}$, has local $(\delta^{-1},\delta/(1+\delta))$-spectral contraction
-- statement:
--   Let $G$ be a finite graph with maximum degree $\Delta$ and girth at least $5$, let $\delta\in(0,1)$, $\beta\in[0,1]$, and let $q\ge2$ be an integer with
--   $$q\ge(1+\delta)(1-\beta)\Delta .$$
--   If $\Delta\ge\delta^{-2}$, then the antiferromagnetic Potts measure on $G$ (interaction matrix $A=\mathbf 1\mathbf 1^\top-(1-\beta)I$, no external field) has local $(\delta^{-1},\delta/(1+\delta))$-spectral contraction in the sense of Condition 4.
--
--   This is the verification of the hypothesis of Theorem 5 that proves Theorem 3.
--
--   Differences from the source:
--   - generalization: for sufficiently large Δ in terms of δ → Δ ≥ δ⁻²; reason: Δ ≥ δ⁻² is the only largeness the proof on pp.32–34 uses ('we may assume Δ ≥ δ⁻²', p.34); every Δ₀(δ) ≥ δ⁻² recovers the source
--   - encoding: the Potts measure µ_{G,q,β} → the Gibbs distribution of A = 11ᵀ − (1 − β)I, λ = 1; reason: §6, p.32; the two weights are equal (proved in the mission's verification file)
--   - encoding: girth at least 5 (∞ for a forest) → 5 ≤ G.egirth; reason: Mathlib's egirth is ⊤ for acyclic graphs, so forests are included
-- source:
--   Chen, Liu, A Spectral Local-to-Global Principle for Spin Systems on Graphs with Girth At Least Five, arXiv:2608.25491, §6, proof of Theorem 3, pp.32–34

import Mathlib
import Definitions.Def_SpinGirth5_gibbsWeight
import Definitions.Def_SpinGirth5_pottsDist

namespace SpinGirth5

/-- **Local spectral contraction of the antiferromagnetic Potts model** (§6). Let `G` be a graph
with maximum degree `Δ` and girth at least 5, `δ ∈ (0, 1)`, `β ∈ [0, 1]`, and `q ≥ 2` an integer
with `q ≥ (1 + δ)(1 − β)Δ`. If `Δ ≥ δ⁻²`, the Potts measure (interaction `A = 11ᵀ − (1 − β)I`, no
external field) has local `(δ⁻¹, δ/(1 + δ))`-spectral contraction.

Chen, Liu, *A Spectral Local-to-Global Principle for Spin Systems on Graphs with Girth At Least
Five*, arXiv:2608.25491, §6, proof of Theorem 3, pp.32–34 ("The estimates above are uniform over
v and all feasible pinnings τ. Thus the Potts measure has local (δ⁻¹, δ/(1 + δ))-spectral
contraction", p.34).

**Formalization Note** The page uses "for sufficiently large Δ in terms of δ, we may assume
Δ ≥ δ⁻²" and nothing else about the size of `Δ`; the threshold `Δ ≥ δ⁻²` is stated explicitly. -/
theorem potts_local_spectral_contraction {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hgirth : 5 ≤ G.egirth) (δ : ℝ) (hδ0 : 0 < δ)
    (hδ1 : δ < 1) (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) (q : ℕ) (hq2 : 2 ≤ q)
    (hq : (1 + δ) * (1 - β) * G.maxDegree ≤ q) (hΔ : δ⁻¹ ^ 2 ≤ G.maxDegree) :
    LocalSpectralContraction G (pottsInteraction q β hβ0 hβ1) δ⁻¹ (δ / (1 + δ)) := by sorry

end SpinGirth5
