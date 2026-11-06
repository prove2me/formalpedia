-- Prove2me | Theorems.Thm_TransvectionMixing_lemma_3_1_degree_of_coefficient_map
-- name    : TransvectionMixing.lemma_3_1_degree_of_coefficient_map
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:19:15.119806+00:00
-- url     : https://prove2.me/theorems/200dade7-e9a1-4627-abd1-d4bc17f26495
-- title:
--   Lemma 3.1 — degree of the coefficient map: total degree $\le H(T,\eta)$ except with probability $\eta/16$
-- statement:
--   Let $T\ge 1$, $0<\eta<1$, and let $\sigma$ be a uniformly random skeleton of length $T$ on $n$ rows. Consider the coefficient product
--   $$
--   (I_n+a_TE_{J_T,I_T})\cdots(I_n+a_1E_{J_1,I_1})
--   $$
--   as a matrix of polynomials in $a_1,\dots,a_T$. Except with probability $\eta/16$, every entry has total degree at most
--   $$
--   H(T,\eta)=\min\Bigl\{T,\ \Bigl\lceil\frac{eT}{n}+\log\frac{16n}{\eta}\Bigr\rceil\Bigr\}.
--   $$
--
--   The degree bound feeds the field threshold $Q_{\mathrm{geom}}$ of Corollary 3.4.
--
--   **Formalization Note** The paper states the bound for the coordinates of $F_\sigma=\mathrm{pr}_Y(\text{product}\cdot X)$; these are linear combinations of the product's entries.
--
--   Differences from the source:
--   - generalization: every coordinate of F_σ = pr_Y(product · X), over 𝔽_q → every entry of the coefficient product, over an arbitrary field; reason: coordinates of F_σ are linear combinations of the entries, so the bound transfers to every X and both targets Y; the degree does not depend on the field
--   - encoding: laws of the walk over uniform skeletons and uniform coefficients → normalized counts (`prob`, `skelLaw`, `entryLaw`, `piS`) over finite types; reason: Lean convention for finite uniform probability; same values
--   - encoding: rows [n] = {1, …, n}; update i ↦ j is left multiplication by Iₙ + aE_{ji} → rows Fin n (0-based); the update is `Matrix.transvection j i a`; reason: Lean indexing; same walk (direction checked in a proved sanity file)
-- source:
--   Braverman, Jain, Newman, Optimal Marginal Mixing for Transvection-Based Trapdoored Matrices over Large Fields (manuscript, sha256 217f833f…), Lemma 3.1, eq. (6), p.9

import Mathlib
import Definitions.Def_TransvectionMixing_walkMat
import Definitions.Def_TransvectionMixing_Tshears

namespace TransvectionMixing

/-- **Lemma 3.1** (degree of the coefficient map) (Braverman–Jain–Newman, *Optimal Marginal Mixing for Transvection-Based Trapdoored Matrices over
Large Fields*, manuscript sha256 217f833f…, §3.1, p.9). Let `T ≥ 1`,
`0 < η < 1`, and let `σ` be a uniform random skeleton of length `T` on `n` rows. Except
with probability `η/16`, every entry of the coefficient product
`(Iₙ + a_T E_{J_T,I_T}) ⋯ (Iₙ + a_1 E_{J_1,I_1})`, a polynomial in `a₁, …, a_T`, has total
degree at most `H(T, η) = min{T, ⌈eT/n + log(16n/η)⌉}`.

**Formalization Note** The paper bounds the coordinates of `F_σ = pr_Y(product · X)`; these are
linear combinations of the product's entries, so the bound on the entries implies it for every
`X` and both targets `Y`. The field is arbitrary. -/
theorem lemma_3_1_degree_of_coefficient_map (F : Type*) [Field F] (n T : ℕ) (hT : 1 ≤ T)
    (η : ℝ) (hη0 : 0 < η) (hη1 : η < 1) :
    prob (fun σ : Skel n T =>
        ¬ ∀ i j, (coeffPoly (F := F) σ i j).totalDegree ≤ Hdeg n T η) ≤ η / 16 := by sorry

end TransvectionMixing
