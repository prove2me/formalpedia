-- Prove2me | Theorems.Thm_TransvectionMixing_lemma_5_6_combining_four_quasi_shears
-- name    : TransvectionMixing.lemma_5_6_combining_four_quasi_shears
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:21:27.346539+00:00
-- url     : https://prove2.me/theorems/34370dd8-4fda-4551-a007-c000c180e41a
-- title:
--   Lemma 5.6 — combining four quasi-shears gives a rational section to $\mathrm{SL}_n$
-- statement:
--   Assume $n\ge 256$. Split a skeleton as $\sigma=\sigma_1\sigma_2\sigma_3\sigma_4$ with source and target sets
--   $$
--   \sigma_1:B_0\to B_1,\qquad\sigma_2:B_1\to B_0,\qquad\sigma_3:B_0\to B_1,\qquad\sigma_4:B_1\setminus\{n\}\to B_0\cup\{n\}.
--   $$
--   If each segment splits into three consecutive sublists satisfying the matching condition of Lemma 5.5 for its source and target sets, then the coefficient-to-endpoint map from $I_n$,
--   $$
--   a\ \longmapsto\ (I_n+a_TE_{J_T,I_T})\cdots(I_n+a_1E_{J_1,I_1}),
--   $$
--   has a rational section $\mathrm{SL}_n\dashrightarrow\mathbb A^T$ over $\mathbb F_q$.
--
--   With Corollary 3.4 this gives full-group mixing (Proposition 5.8).
--
--   **Formalization Note** Segment $j$ is $\tau_{j1}\tau_{j2}\tau_{j3}$ with arbitrary lengths; the rational section lives in the function field $\mathbb F_q(\mathrm{SL}_n)$.
--
--   Differences from the source:
--   - encoding: rational section over 𝔽_q of the coefficient-to-endpoint map → `HasRationalSectionSL (coeffPoly σ)`: a tuple in 𝔽_q(SLₙ) at which the polynomial walk matrix is the generic matrix; reason: same notion (see the definition)
--   - encoding: rows [n] = {1, …, n}; update i ↦ j is left multiplication by Iₙ + aE_{ji} → rows Fin n (0-based); the update is `Matrix.transvection j i a`; reason: Lean indexing; same walk (direction checked in a proved sanity file)
-- source:
--   Braverman, Jain, Newman, Optimal Marginal Mixing for Transvection-Based Trapdoored Matrices over Large Fields (manuscript, sha256 217f833f…), Lemma 5.6, p.27 (table of segments and Lemma 5.5, p.26; standing n ≥ 256, p.25)

import Mathlib
import Definitions.Def_TransvectionMixing_walkMat
import Definitions.Def_TransvectionMixing_HasRationalSectionSL
import Definitions.Def_TransvectionMixing_MatchingCond

namespace TransvectionMixing

/-- **Lemma 5.6** (combining four quasi-shears) (Braverman–Jain–Newman, *Optimal Marginal Mixing for Transvection-Based Trapdoored Matrices over
Large Fields*, manuscript sha256 217f833f…, §5.3.2, p.27). Assume `n ≥ 256`
(standing in §5.3). Split a skeleton as `σ = σ₁σ₂σ₃σ₄` with source and target sets
`σ₁ : B₀ → B₁`, `σ₂ : B₁ → B₀`, `σ₃ : B₀ → B₁`, `σ₄ : B₁ ∖ {n} → B₀ ∪ {n}` (table, p.26). If each
segment splits into three sublists satisfying the matching condition of Lemma 5.5, then the
coefficient-to-endpoint map from `Iₙ` to `SLₙ` has a rational section over `𝔽_q`.

**Formalization Note** Segment `j` is `τ_{j1} τ_{j2} τ_{j3}` of arbitrary lengths; the
coefficient-to-endpoint map from `Iₙ` is the polynomial matrix `coeffPoly σ`. -/
theorem lemma_5_6_combining_four_quasi_shears (F : Type*) [Field F] [Fintype F] (n : ℕ)
    (hn : 256 ≤ n) {a₁ b₁ c₁ a₂ b₂ c₂ a₃ b₃ c₃ a₄ b₄ c₄ : ℕ}
    (τ₁₁ : Skel n a₁) (τ₁₂ : Skel n b₁) (τ₁₃ : Skel n c₁)
    (τ₂₁ : Skel n a₂) (τ₂₂ : Skel n b₂) (τ₂₃ : Skel n c₂)
    (τ₃₁ : Skel n a₃) (τ₃₂ : Skel n b₃) (τ₃₃ : Skel n c₃)
    (τ₄₁ : Skel n a₄) (τ₄₂ : Skel n b₄) (τ₄₃ : Skel n c₄)
    (h₁ : MatchingCond (B0 n) (B1 n) τ₁₁ τ₁₂ τ₁₃) (h₂ : MatchingCond (B1 n) (B0 n) τ₂₁ τ₂₂ τ₂₃)
    (h₃ : MatchingCond (B0 n) (B1 n) τ₃₁ τ₃₂ τ₃₃) (h₄ : MatchingCond (B1' n) (B0' n) τ₄₁ τ₄₂ τ₄₃) :
    HasRationalSectionSL (coeffPoly (F := F)
      ((((seg3 τ₁₁ τ₁₂ τ₁₃).append (seg3 τ₂₁ τ₂₂ τ₂₃)).append (seg3 τ₃₁ τ₃₂ τ₃₃)).append
        (seg3 τ₄₁ τ₄₂ τ₄₃))) := by sorry

end TransvectionMixing
