-- Prove2me | Theorems.Thm_PPRInstOpt_UnknownN_lemma_3_6
-- name    : PPRInstOpt.UnknownN.lemma_3_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T17:13:45.0262+00:00
-- url     : https://prove2.me/theorems/15c7dd65-50e3-42ab-9242-2322f49896bc
-- title:
--   Lemma 3.6 — backward freezing loses at most εr π(s,t)/8
-- statement:
--   Run Algorithm 7 from $t$ with budget $\kappa_b\ge1$, activating a vertex when $r_b(v)\ge\alpha\bar r_b/2$ and freezing it $L_b=\lceil\log_{1-\alpha/2}(\varepsilon_r\alpha^2/(32\kappa_b))\rceil$ iterations later. At the end, for every vertex $s$,
--   $$\sum_{v\in F_b}\pi(s,v)\,r_b(v)\le\frac{\varepsilon_r\,\pi(s,t)}{8}.$$
--
--   Differences from the source:
--   - reading: conclusion '≤ επ(s, t)/8' → εr π(s, t)/8; reason: the ε of the conclusion is the εr of L_b
--   - encoding: budget κ → natural number κ ≥ 1; reason: L_f and L_b divide by κ; Algorithm 8 only uses κ = 2^i
--   - reading: εr a constant relative error → 0 < εr < 1; reason: εr ≥ 1 makes the output 0 always correct; the paper's constant-factor estimation needs εr < 1
--   - reading: candidate set {u ∈ V \ F : threshold} ∪ (C^(ℓ−1) \ F) → only vertices with positive residue are activated; reason: finding I1: with threshold 0 the printed set contains unreached vertices, not computable without n; for a positive threshold the sets coincide
--   - encoding: π(u, v) = probability that the α-discounted walk from u terminates at v → ppr α G u v = Σ_k α(1−α)^k P^k(u, v); reason: the paper's own equivalent form (p. 3); same values
--   - encoding: directed simple graph with every out-degree ≥ 1 and fixed adjacency lists → Digraph V over an arbitrary vertex type: duplicate-free out- and in-lists describing one edge set, no self-loops, nonempty out-lists; reason: same instances; list order fixes out(v, i) and in(v, i)
-- source:
--   Bertram, Jensen, Thorup, Wang, Yan, Instance-Optimality of Single-Pair Personalized PageRank, STOC 2027 submission (manuscript sha256 e1dc6b7d…), p. 22, Lemma 3.6

import Mathlib
import Definitions.Def_PPRInstOpt_UnknownN_Freezing

namespace PPRInstOpt.UnknownN

/-- Lemma 3.6 (p. 22): at the end of Algorithm 7 (budget `κ_b ≥ 1`, freezing after
`L_b = ⌈log_{1-α/2}(εr α²/(32κ_b))⌉` rounds), for every vertex `s`,
`Σ_{v ∈ F_b} π(s, v) r_b(v) ≤ εr π(s, t)/8`. -/
theorem lemma_3_6 {V : Type} [Fintype V] [DecidableEq V] (α εr : ℝ) (hα0 : 0 < α) (hα1 : α < 1)
    (hε0 : 0 < εr) (hε1 : εr < 1) (G : Digraph V) (s t : V) (κ : ℕ) (hκ : 1 ≤ κ) :
    ∑ v ∈ Finset.univ.filter (fun v => (bwdFinal G.oracle α εr κ t).frozen v = true),
        ppr α G s v * (bwdFinal G.oracle α εr κ t).r v ≤ εr * ppr α G s t / 8 := by sorry

end PPRInstOpt.UnknownN
