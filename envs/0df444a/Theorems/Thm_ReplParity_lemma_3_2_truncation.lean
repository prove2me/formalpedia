-- Prove2me | Theorems.Thm_ReplParity_lemma_3_2_truncation
-- name    : ReplParity.lemma_3_2_truncation
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:40:39.394608+00:00
-- url     : https://prove2.me/theorems/987e02e7-037c-498e-8880-34e0164fc735
-- title:
--   Proof of Lemma 3.2, p.16 — truncations differ by at most the token sets
-- statement:
--   1. Let $T,T'$ be finite sets with $|T|=|T'|=K$, ordered by a common key that is injective on $T\cup T'$, let $\kappa\le K$, and let $B,B'$ be their first $\kappa$ elements. With $u=|B\setminus T'|$ and $v=|B'\setminus T|$ (the kept tokens outside $T\cap T'$),
--   $$|B\triangle B'|=2\max(u,v)\le|T\triangle T'| .$$
--   2. For any two sequences $S,S'$ of vectors in $\mathbb F_2^n$, the token sets satisfy
--   $$|\mathcal T(S)\triangle\mathcal T(S')|=\sum_V\dim(V)\,|n_S(V)-n_{S'}(V)|\le n\,\|F(S)-F(S')\|_1 .$$
--
--   Combined with Lemma 3.1 these bound the expected difference of the truncated token sets in the replicability proof of Lemma 3.2.
--
--   Differences from the source:
--   - generalization: T = T(S), T′ = T(S′) ordered by the token rule → any finite sets of equal size K with any common key injective on T ∪ T′; reason: specializes to the token sets and the token order
--   - generalization: token sets of two samples of size K from Q on nonzero vectors → token sets of any two finite sequences; reason: the identity and the bound hold for every pair of sequences
--   - encoding: u and v, the kept tokens outside C = T ∩ T′; ∥F(S) − F(S′)∥₁ → u = |B \ T′|, v = |B′ \ T|; Σ_V |n_S(V) − n_S′(V)|; reason: B ⊆ T, so B \ C = B \ T′; same quantities
-- source:
--   Shen, Zhong, Replicable Parity Learning: Cubic Sample Complexity and a Geometric Characterization, STOC 2027 submission (manuscript sha256 40424491d00eef39c790dd41b7557e0ffdf9de2d14d95ddcd611aeacb0f77a50), proof of Lemma 3.2, p.16 (PDF p.18)

import Mathlib
import Definitions.Def_ReplParity_tokens

namespace ReplParity

open Classical in
/-- **Truncation and token differences (proof of Lemma 3.2).** Shen, Zhong, *Replicable Parity
Learning: Cubic Sample Complexity and a Geometric Characterization*, STOC 2027 submission (manuscript
sha256 40424491…), proof of Lemma 3.2, p.16 (PDF p.18): "Let T = T(S) and T′ = T(S′), which both
have K elements and are ordered by the same rule. Let C = T ∩ T′, and suppose that the two
truncations keep u and v tokens outside C. Then the common tokens that they keep are the first
κ − u and the first κ − v elements of C, and hence |B(S)△B(S′)| = 2 max(u, v) ≤ |T△T′|. Moreover
|T△T′| = Σ_V dim(V) |n_S(V) − n_S′(V)| ≤ n∥F(S) − F(S′)∥₁".

(a) For finite sets `T`, `T′` of the same size `K`, ordered by a common key injective on `T ∪ T′`,
with first-`κ` truncations `B`, `B′` (`κ ≤ K`), `u = |B \ T′|`, `v = |B′ \ T|`:
`|B △ B′| = 2 max(u, v) ≤ |T △ T′|`.
(b) For the token sets of two sequences `S`, `S′` of vectors in 𝔽ⁿ₂:
`|T(S) △ T(S′)| = Σ_V dim(V) |n_S(V) − n_{S′}(V)| ≤ n Σ_V |n_S(V) − n_{S′}(V)|`. -/
theorem lemma_3_2_truncation :
    (∀ {τ τ' : Type} [DecidableEq τ] [LinearOrder τ'] (key : τ → τ') (T T' : Finset τ) (K κ : ℕ),
      Set.InjOn key (↑(T ∪ T') : Set τ) → T.card = K → T'.card = K → κ ≤ K →
      (symmDiff (firstK key κ T) (firstK key κ T')).card =
          2 * max (firstK key κ T \ T').card (firstK key κ T' \ T).card ∧
        2 * max (firstK key κ T \ T').card (firstK key κ T' \ T).card ≤ (symmDiff T T').card) ∧
    (∀ (n : ℕ) (S S' : List (Vec n)),
      ((symmDiff (tokens S) (tokens S')).card : ℤ) =
          ∑ V : Subsp n, (Module.finrank (ZMod 2) V : ℤ) * |(mult S V : ℤ) - mult S' V| ∧
        ∑ V : Subsp n, (Module.finrank (ZMod 2) V : ℤ) * |(mult S V : ℤ) - mult S' V| ≤
          n * ∑ V : Subsp n, |(mult S V : ℤ) - mult S' V|) := by sorry

end ReplParity
