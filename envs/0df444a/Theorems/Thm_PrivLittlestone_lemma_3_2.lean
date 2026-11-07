-- Prove2me | Theorems.Thm_PrivLittlestone_lemma_3_2
-- name    : PrivLittlestone.lemma_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T03:38:06.205561+00:00
-- url     : https://prove2.me/theorems/833ccaa7-0f66-44c8-a0f8-778a619674c6
-- title:
--   Lemma 3.2 — batch inequality $Z_{S_b}/Z_{S_0} \le \mathbb E_{Q_{S_0}} e^{-\eta\sum_i \ell_{u_i}} + (1+\gamma)^b - 1$
-- statement:
--   Let a ranked candidate system of height $D$ and branching parameter $B$ be given, and let $\eta, a > 0$. Let $S_i = S_0 u_1 \cdots u_i$ for $0 \le i \le b$; no monotonicity of the candidate sets $C(S_i)$ is assumed. Then
--   $$
--   \frac{Z_{S_b}}{Z_{S_0}} \le \mathbb E_{h \sim Q_{S_0}} \exp\Big( -\eta \sum_{i=1}^{b} \ell_{u_i}(h) \Big) + (1 + \gamma)^b - 1 ,
--   $$
--   with $\gamma = e^{\eta}\sum_{j=1}^{D} B^j e^{-aj}$.
--
--   The inequality separates the surviving weight from the newly added weight; cumulative losses account for candidates that disappear and reenter.
--
--   Differences from the source: none.
-- source:
--   He–He, Private Online Learning of Littlestone Classes and Matroid Flats, STOC 2027 submission (manuscript sha256 21480556…c562), Lemma 3.2, (3), p.6

import Mathlib
import Definitions.Def_PrivLittlestone_gibbsExp
import Definitions.Def_PrivLittlestone_gammaTerm

namespace PrivLittlestone

/-- **Lemma 3.2 (Batch inequality)** (He–He, *Private Online Learning of Littlestone Classes and
Matroid Flats*, STOC 2027 submission manuscript (sha256 21480556…c562), Lemma 3.2, (3), p.6).
For a ranked candidate system and `η, a > 0`, let `S_i = S_0 u_1 ⋯ u_i` for `0 ≤ i ≤ b`; no
monotonicity of `C(S_i)` is assumed. Then
`Z_{S_b}/Z_{S_0} ≤ E_{h∼Q_{S_0}} exp(−η ∑_{i=1}^b ℓ_{u_i}(h)) + (1 + γ)^b − 1`. -/
theorem lemma_3_2 {Z U : Type*} {D : ℕ} {B : ℝ} (sys : RankedCandidateSystem Z U D B)
    (η a : ℝ) (hη : 0 < η) (ha : 0 < a) (S₀ us : List Z) :
    potential sys η a (S₀ ++ us) / potential sys η a S₀ ≤
      gibbsExp sys η a S₀ (fun h => Real.exp (-η * (us.map fun u => (sys.loss u h : ℝ)).sum)) +
        (1 + gammaTerm η a B D) ^ us.length - 1 := by sorry

end PrivLittlestone
