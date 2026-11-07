-- Prove2me | Theorems.Thm_ReplParity_lemma_3_1
-- name    : ReplParity.lemma_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:40:06.310738+00:00
-- url     : https://prove2.me/theorems/c5b9805a-20fa-4418-877b-7f88c8541ca2
-- title:
--   Lemma 3.1 — second moment of multiplicity differences
-- statement:
--   Let $Q$ be a distribution on $\mathbb F_2^n$, let $S,S'\sim Q^m$ be independent samples of size $m$, with zero vectors discarded before partitioning, and let $\Delta=F(S)-F(S')$, i.e. $\Delta_V=n_S(V)-n_{S'}(V)$ for every subspace $V$. Then
--   $$\mathbb E\|\Delta\|_2^2\le4m\qquad\text{and}\qquad\mathbb E\|\Delta\|_1\le\sqrt{8nm}.$$
--
--   This second-moment bound is what makes the token min-hash of Lemma 3.2 replicable.
--
--   Differences from the source:
--   - encoding: ∥∆∥₂², ∥∆∥₁ and E over S, S′ → Σ_V ∆_V², Σ_V |∆_V| over all subspaces V, and the finite sum weighted by ∏ Q(Sᵢ) ∏ Q(S′ᵢ); reason: same quantities
-- source:
--   Shen, Zhong, Replicable Parity Learning: Cubic Sample Complexity and a Geometric Characterization, STOC 2027 submission (manuscript sha256 40424491d00eef39c790dd41b7557e0ffdf9de2d14d95ddcd611aeacb0f77a50), Lemma 3.1, p.15 (PDF p.17)

import Mathlib
import Definitions.Def_ReplParity_mult
import Definitions.Def_ReplParity_prIID

namespace ReplParity

/-- **Lemma 3.1 (second moment of multiplicity differences).** Shen, Zhong, *Replicable Parity
Learning: Cubic Sample Complexity and a Geometric Characterization*, STOC 2027 submission (manuscript
sha256 40424491…), Lemma 3.1, p.15 (PDF p.17): "Let S and S′ be independent samples of size m from a
distribution on 𝔽ⁿ₂, with zero vectors discarded before partitioning, and let ∆ = F(S) − F(S′).
Then E∥∆∥₂² ≤ 4m and E∥∆∥₁ ≤ √(8nm)."

Here `∆_V = n_S(V) − n_{S′}(V)` for every subspace `V`, `∥∆∥₂² = Σ_V ∆_V²`, `∥∆∥₁ = Σ_V |∆_V|`, and
the expectation is over independent `S, S′ ∼ Q^m`. -/
theorem lemma_3_1 (n m : ℕ) (Q : PMF (Vec n)) :
    expIID2 Q m (fun S S' =>
        ∑ V : Subsp n, ((mult (List.ofFn S) V : ℝ) - mult (List.ofFn S') V) ^ 2) ≤ 4 * m ∧
    expIID2 Q m (fun S S' =>
        ∑ V : Subsp n, |(mult (List.ofFn S) V : ℝ) - mult (List.ofFn S') V|) ≤
      Real.sqrt (8 * n * m) := by sorry

end ReplParity
