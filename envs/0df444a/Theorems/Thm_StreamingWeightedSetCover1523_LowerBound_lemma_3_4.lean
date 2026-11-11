-- Prove2me | Theorems.Thm_StreamingWeightedSetCover1523_LowerBound_lemma_3_4
-- name    : StreamingWeightedSetCover1523.LowerBound.lemma_3_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:08:18.954771+00:00
-- url     : https://prove2.me/theorems/0cbe40ee-9488-4bcc-afdf-26df243e80e0
-- title:
--   Lemma 3.4 — acceptance gap of short randomized protocols (13)
-- statement:
--   Let $k\ge8$ and let $A$ be a good matrix. Consider a randomized protocol: input-independent coins $\omega$ from a probability space (covering public and private randomness), each selecting a deterministic protocol tree of depth at most $b$ on Alice's block $V_{\le r}$ and Bob's block $V_{>r}$, with the leaf label as decision. Then
--   $$\Big|\Pr_{P_1^A}[\text{accept}]-\Pr_{P_0^A}[\text{accept}]\Big|\ \le\ \varepsilon+\frac{120\,b\ln2}{d\min(r,s)}.\qquad(13)$$
--   Consequently, if the gap is at least $\varepsilon+\delta$ for some $\delta>0$, then
--   $$b\ \ge\ \frac{\delta\,d\,M}{360\ln 2},$$
--   the explicit form of "a constant gap larger than $\varepsilon$ requires $\Omega(Md)$ bits".
--
--   Differences from the source:
--   - generalization: at most b communicated bits including the final decision bit → trees of depth at most b whose leaves carry the decision without charge; reason: a source protocol whose last bit is its decision is a tree of depth ≤ b with leaves labelled by that bit; the proof uses only ≤ 2^b leaves
--   - generalization: a good matrix under the standing parameters of §2 → a good matrix with k ≥ 8, arbitrary v and M, including the degenerate cases d = 0 or min(r,s) = 0 (division by 0 read as 0); reason: the proof uses only goodness and Lemma 3.3; for d ≥ 1 and M ≥ 2 it is (13)
--   - encoding: Thus a constant gap larger than ε requires Ω(Md) bits when the blocks are balanced → for every δ > 0, gap ≥ ε + δ implies δ·d·M ≤ 360 ln 2 · b; reason: the finite rearrangement of (13) using min(r,s) ≥ M/3, which makes the Ω explicit
--   - encoding: randomized protocol with public and private coins → a probability space of coins selecting deterministic trees, with measurable acceptance events; reason: fixing all coins leaves a deterministic tree; genuine protocols have measurable events
--   - encoding: vectors in F₂^v, a v×M binary matrix, U=[v]×{0,1}, identifiers C_1..C_M, E_1..E_M, indices 1..M → Fin v → ZMod 2, Fin v → Fin M → Bool, Fin v × ZMod 2, Fin M ⊕ Fin M, 0-based indices (left block = indices 0..r−1); reason: finite relabelling of the same objects; no instance changes
-- source:
--   Ali Vakilian, Streaming Weighted Set Cover Requires (Nearly) Linear Space, STOC 2027 submission #1523 (October 2026), Lemma 3.4, printed p. 14 (PDF p. 15), eq. (13); citation basis: submitted artifact, sha256 16f3c2dfc6183f4752aece654f17f2cb6a47fbe55659e6906ad7bd3524d6223f

import Definitions.Def_StreamingWeightedSetCover1523_LowerBound_HardInstance

open MeasureTheory Filter Topology
open scoped BigOperators ENNReal

namespace StreamingWeightedSetCover1523.LowerBound

/-- Lemma 3.4 (PDF p. 15, eq. (13)): fix a good matrix `A` (with `k ≥ 8`). A randomized protocol
(input-independent coins `ω ∼ P`, each selecting a deterministic tree of depth at most `b` on
Alice's block and Bob's block) has acceptance gap
`|Pr_{P₁^A}[accept] - Pr_{P₀^A}[accept]| ≤ ε + 120 b ln 2 / (d min(r,s))`; consequently a gap of at
least `ε + δ`, `δ > 0`, forces `b ≥ δ d M / (360 ln 2)`. -/
theorem lemma_3_4 (v M k : ℕ) (hk : 8 ≤ k) (A : Mat v M) (hA : Good k A) (b : ℕ)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (tree : Ω → DetCCHard.Protocol (Fin (M / 2) → Vec v) (Fin (M - M / 2) → Vec v))
    (hdepth : ∀ ω, (tree ω).depth ≤ b)
    (hmeas : ∀ x y, MeasurableSet {ω | (tree ω).eval x y = true}) :
    |acceptProb (yesLaw k A) blocks P tree - acceptProb (noLaw (v := v) (M := M)) blocks P tree| ≤
        eps k v M + 120 * (b : ℝ) * Real.log 2 /
          ((dParam k v : ℝ) * ((min (M / 2) (M - M / 2) : ℕ) : ℝ)) ∧
      ∀ δ : ℝ, 0 < δ →
        eps k v M + δ ≤
            |acceptProb (yesLaw k A) blocks P tree -
              acceptProb (noLaw (v := v) (M := M)) blocks P tree| →
          δ * (dParam k v : ℝ) * (M : ℝ) ≤ 360 * Real.log 2 * (b : ℝ) := by sorry

end StreamingWeightedSetCover1523.LowerBound
