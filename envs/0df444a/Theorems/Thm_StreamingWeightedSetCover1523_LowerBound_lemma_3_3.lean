-- Prove2me | Theorems.Thm_StreamingWeightedSetCover1523_LowerBound_lemma_3_3
-- name    : StreamingWeightedSetCover1523.LowerBound.lemma_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:08:17.566278+00:00
-- url     : https://prove2.me/theorems/7d515131-7d72-4756-b87c-16028fb083e5
-- title:
--   Lemma 3.3 — rectangle bound (11)
-- statement:
--   Let $k\ge8$ and let $A$ be a good matrix. Alice holds $V_{\le r}$ and Bob $V_{>r}$, $r=\lfloor M/2\rfloor$, $s=M-r$. For any sets $R$ of left-block tuples and $T$ of right-block tuples whose rectangle has NO probability $q_*=P_0^A(R\times T)>0$,
--   $$P_1^A(R\times T)\ \ge\ q_*\Big(1-\varepsilon-\frac{120}{d\,\min(r,s)}\ln\frac1{q_*}\Big).\qquad(11)$$
--
--   $R$ and $T$ are arbitrary sets of whole tuples. Every rectangle is nearly as likely under YES as under NO unless it is very unlikely under NO.
--
--   Differences from the source:
--   - generalization: a good matrix A under the standing parameters of §2 ((1), k ≥ 8) → a good matrix A with k ≥ 8, arbitrary v and M; reason: the proof uses only goodness and the explicit samplers; specializes to the source regime
--   - generalization: d ≥ 1 and r, s ≥ 1 (true in the regime of (1)) → also the degenerate cases d = 0 or min(r,s) = 0, with 120/0 read as 0 both in (9) and in (11); reason: the same argument applies with that convention; for d ≥ 1 and M ≥ 2 the Lean statement is exactly (11)
--   - encoding: vectors in F₂^v, a v×M binary matrix, U=[v]×{0,1}, identifiers C_1..C_M, E_1..E_M, indices 1..M → Fin v → ZMod 2, Fin v → Fin M → Bool, Fin v × ZMod 2, Fin M ⊕ Fin M, 0-based indices (left block = indices 0..r−1); reason: finite relabelling of the same objects; no instance changes
-- source:
--   Ali Vakilian, Streaming Weighted Set Cover Requires (Nearly) Linear Space, STOC 2027 submission #1523 (October 2026), Lemma 3.3, printed p. 13 (PDF p. 14), eq. (11); standing assumption of §3 (PDF p. 13); citation basis: submitted artifact, sha256 16f3c2dfc6183f4752aece654f17f2cb6a47fbe55659e6906ad7bd3524d6223f

import Definitions.Def_StreamingWeightedSetCover1523_LowerBound_HardInstance

open MeasureTheory Filter Topology
open scoped BigOperators ENNReal

namespace StreamingWeightedSetCover1523.LowerBound

/-- Lemma 3.3 (PDF p. 14, eq. (11)): fix a good matrix `A` (with `k ≥ 8`). For any rectangle
`R × T` of the two blocks with NO probability `q* = P₀^A(R × T) > 0`,
`P₁^A(R × T) ≥ q* (1 - ε - (120 / (d min(r,s))) ln(1/q*))`. -/
theorem lemma_3_3 (v M k : ℕ) (hk : 8 ≤ k) (A : Mat v M) (hA : Good k A)
    (R : Set (Fin (M / 2) → Vec v)) (T : Set (Fin (M - M / 2) → Vec v))
    (hq : 0 < rectProb (noLaw (v := v) (M := M)) R T) :
    rectProb (noLaw (v := v) (M := M)) R T *
        (1 - eps k v M -
          120 / ((dParam k v : ℝ) * ((min (M / 2) (M - M / 2) : ℕ) : ℝ)) *
            Real.log (1 / rectProb (noLaw (v := v) (M := M)) R T)) ≤
      rectProb (yesLaw k A) R T := by sorry

end StreamingWeightedSetCover1523.LowerBound
