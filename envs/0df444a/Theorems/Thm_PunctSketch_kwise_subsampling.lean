-- Prove2me | Theorems.Thm_PunctSketch_kwise_subsampling
-- name    : PunctSketch.kwise_subsampling
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:44:52.994495+00:00
-- url     : https://prove2.me/theorems/9b4e7980-6a87-4a14-a929-abffaae86e26
-- title:
--   §5.3, p.19 — $O(k)$-wise independent subsampling suffices
-- statement:
--   There is a constant $t_0$ such that for $k\ge1$, $d\ge33k$ and a level $l$ with
--   $$\frac{33k}{4}\le d\,2^{-l}<\frac{33k}{2},$$
--   and for $t_0k$-wise independent indicators $X_1,\dots,X_d$ on a uniform finite space, each of mean $2^{-l}$,
--   $$\Pr\Big[0<\sum_iX_i\le33k\Big]\ge1-e^{-2k}.$$
--   This is the concentration step of Lemma 5.1 with limited independence, which is what allows the streaming algorithm to store its subsampling coins.
--
--   Differences from the source:
--   - reading: "handled using an O(k)-wise independent hash function" → the concentration bound of the proof of Lemma 5.1 under t₀k-wise independence, with t₀ existential; reason: the sentence asserts this without a constant, and this is the property the hash has to deliver
--   - encoding: an O(k)-wise independent hash function → indicators on any finite uniform space (such as seeds of a hash family); reason: covers every such hash
-- source:
--   Çekirge, Chakrabarti, Dutta, McGregor, Vinayak, Puncturable Graph Sketches and the Complexity of Distributed Vertex Connectivity, STOC 2027 submission (manuscript sha256 a630f88815653b5f1b35579cbfa2100b617a4d540f009489027b8c55f65e1a2c), §5.3, p.19 (PDF p.20); proof of Lemma 5.1, pp.16–17 (PDF pp.17–18)

import Mathlib
import Definitions.Def_PunctSketch_IsKWiseIndep

namespace PunctSketch

/-- **`O(k)`-wise independent subsampling.** Çekirge, Chakrabarti, Dutta, McGregor, Vinayak, *Puncturable Graph Sketches and the Complexity of Distributed Vertex Connectivity*, STOC 2027 submission (manuscript sha256 a630f888…), §5.3, p.19: "The random graph subsamples can be handled
using an O(k)-wise independent hash function instead of being picked truly randomly".

There is a constant `t₀` such that for every `k ≥ 1`, every `d ≥ 33k` and every level `l` with
`33k/4 ≤ d 2^{−l} < 33k/2`: for `t₀k`-wise independent indicators of marginal `2^{−l}` on `d` boundary edges,
`Pr[0 < d_l ≤ 33k] ≥ 1 − e^{−2k}`, the bound of the proof of Lemma 5.1, p.17.

**Formalization Note.** The source only asserts `O(k)`-wise independence, so `t₀` is existential. The coin
space is any finite uniform space, such as the seeds of a hash family. -/
theorem kwise_subsampling :
    ∃ t₀ : ℕ, ∀ (k d l : ℕ) {Ω : Type} [Fintype Ω] [Nonempty Ω], 1 ≤ k → 33 * k ≤ d →
      33 * (k : ℝ) / 4 ≤ (d : ℝ) * (2 : ℝ)⁻¹ ^ l → (d : ℝ) * (2 : ℝ)⁻¹ ^ l < 33 * (k : ℝ) / 2 →
      ∀ X : Fin d → Ω → Bool, IsKWiseIndep X (t₀ * k) →
        (∀ i, coinProb (fun ω => X i ω = true) = (2 : ℝ)⁻¹ ^ l) →
        1 - Real.exp (-(2 * (k : ℝ))) ≤
          coinProb (fun ω =>
            0 < (Finset.univ.filter (fun i => X i ω = true)).card ∧
              (Finset.univ.filter (fun i => X i ω = true)).card ≤ 33 * k) := by sorry

end PunctSketch
