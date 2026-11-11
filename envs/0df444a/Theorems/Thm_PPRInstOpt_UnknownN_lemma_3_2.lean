-- Prove2me | Theorems.Thm_PPRInstOpt_UnknownN_lemma_3_2
-- name    : PPRInstOpt.UnknownN.lemma_3_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T17:13:35.471909+00:00
-- url     : https://prove2.me/theorems/f7077c06-9bb1-48e8-917f-a9ff949036c8
-- title:
--   Lemma 3.2 — forward freezing loses at most εr π(s,t)/8
-- statement:
--   Run Algorithm 6 from $s$ with budget $\kappa_f\ge1$, activating a vertex when $r_f(u)/d_{\mathrm{out}}(u)\ge R_f/\kappa_f$ and freezing it $L_f=\lceil\log_{1-\alpha/2}(\varepsilon_r/(8\kappa_f^2))\rceil$ iterations later. At the end, for every vertex $t$,
--   $$\sum_{u\in F_f}r_f(u)\,\pi(u,t)\le\frac{\varepsilon_r\,\pi(s,t)}{8}.$$
--   This bounds the mass that freezing hides from the estimator (Lemma 4.2).
--
--   Differences from the source:
--   - reading: conclusion '≤ επ(s, t)/8' → εr π(s, t)/8; reason: the ε of the conclusion is the εr of L_f
--   - encoding: budget κ → natural number κ ≥ 1; reason: L_f and L_b divide by κ; Algorithm 8 only uses κ = 2^i
--   - reading: εr a constant relative error → 0 < εr < 1; reason: εr ≥ 1 makes the output 0 always correct; the paper's constant-factor estimation needs εr < 1
--   - reading: candidate set {u ∈ V \ F : threshold} ∪ (C^(ℓ−1) \ F) → only vertices with positive residue are activated; reason: finding I1: with threshold 0 the printed set contains unreached vertices, not computable without n; for a positive threshold the sets coincide
--   - encoding: π(u, v) = probability that the α-discounted walk from u terminates at v → ppr α G u v = Σ_k α(1−α)^k P^k(u, v); reason: the paper's own equivalent form (p. 3); same values
--   - encoding: directed simple graph with every out-degree ≥ 1 and fixed adjacency lists → Digraph V over an arbitrary vertex type: duplicate-free out- and in-lists describing one edge set, no self-loops, nonempty out-lists; reason: same instances; list order fixes out(v, i) and in(v, i)
-- source:
--   Bertram, Jensen, Thorup, Wang, Yan, Instance-Optimality of Single-Pair Personalized PageRank, STOC 2027 submission (manuscript sha256 e1dc6b7d…), p. 17, Lemma 3.2

import Mathlib
import Definitions.Def_PPRInstOpt_UnknownN_Freezing

namespace PPRInstOpt.UnknownN

/-- Lemma 3.2 (p. 17): at the end of Algorithm 6 (budget `κ_f ≥ 1`, freezing after
`L_f = ⌈log_{1-α/2}(εr/(8κ_f²))⌉` rounds), for every vertex `t`,
`Σ_{u ∈ F_f} r_f(u) π(u, t) ≤ εr π(s, t)/8`. -/
theorem lemma_3_2 {V : Type} [Fintype V] [DecidableEq V] (α εr : ℝ) (hα0 : 0 < α) (hα1 : α < 1)
    (hε0 : 0 < εr) (hε1 : εr < 1) (G : Digraph V) (s t : V) (κ : ℕ) (hκ : 1 ≤ κ) :
    ∑ u ∈ Finset.univ.filter (fun u => (fwdFinal G.oracle α εr κ s).frozen u = true),
        (fwdFinal G.oracle α εr κ s).r u * ppr α G u t ≤ εr * ppr α G s t / 8 := by sorry

end PPRInstOpt.UnknownN
