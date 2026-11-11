-- Prove2me | Theorems.Thm_PPRInstOpt_UnknownN_lemma_3_1
-- name    : PPRInstOpt.UnknownN.lemma_3_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T17:13:32.451562+00:00
-- url     : https://prove2.me/theorems/205de0b6-8f69-418e-b6ac-5622695cf401
-- title:
--   Lemma 3.1 — the non-frozen forward residue decays by (1 − α/2) per iteration
-- statement:
--   Run Algorithm 6 (ForwardPushWithFreezing) from $s$ with budget $\kappa_f\ge 1$ on a valid graph, and let $r^{(\ell)}$, $F^{(\ell)}$ be the residues and frozen set after $\ell$ completed iterations and $R^{(\ell)}=\sum_{u\notin F^{(\ell)}}r^{(\ell)}(u)$. If $\ell$ iterations were completed then
--   $$R^{(\ell)}\le(1-\alpha/2)^{\ell},$$
--   and if $\ell+1$ iterations were completed then $R^{(\ell+1)}\le(1-\alpha/2)R^{(\ell)}$. The algorithm pushes only when $\sum_{C^{(\ell)}}r\ge R/2$, which drives this geometric decay.
--
--   Differences from the source:
--   - reading: superscript (ℓ) = beginning of iteration ℓ, for each ℓ ≥ 0 → state after ℓ completed iterations, for ℓ up to the number of iterations Algorithm 6 performs; reason: §3.1 counts iterations from 0 (base case R^(0) = 1) while Algorithm 6 numbers them from 1 (finding I4); the lemma speaks of iterations that were performed
--   - encoding: budget κ → natural number κ ≥ 1; reason: L_f and L_b divide by κ; Algorithm 8 only uses κ = 2^i
--   - reading: εr a constant relative error → 0 < εr < 1; reason: εr ≥ 1 makes the output 0 always correct; the paper's constant-factor estimation needs εr < 1
--   - reading: candidate set {u ∈ V \ F : threshold} ∪ (C^(ℓ−1) \ F) → only vertices with positive residue are activated; reason: finding I1: with threshold 0 the printed set contains unreached vertices, not computable without n; for a positive threshold the sets coincide
--   - encoding: π(u, v) = probability that the α-discounted walk from u terminates at v → ppr α G u v = Σ_k α(1−α)^k P^k(u, v); reason: the paper's own equivalent form (p. 3); same values
--   - encoding: directed simple graph with every out-degree ≥ 1 and fixed adjacency lists → Digraph V over an arbitrary vertex type: duplicate-free out- and in-lists describing one edge set, no self-loops, nonempty out-lists; reason: same instances; list order fixes out(v, i) and in(v, i)
-- source:
--   Bertram, Jensen, Thorup, Wang, Yan, Instance-Optimality of Single-Pair Personalized PageRank, STOC 2027 submission (manuscript sha256 e1dc6b7d…), p. 17, Lemma 3.1

import Mathlib
import Definitions.Def_PPRInstOpt_UnknownN_Freezing

namespace PPRInstOpt.UnknownN

/-- Lemma 3.1 (p. 17): in every run of Algorithm 6 (any graph, source `s`, budget `κ_f ≥ 1`), with
`R^(ℓ) = Σ_{u ∉ F^(ℓ)} r^(ℓ)(u)` after `ℓ` completed iterations: `R^(ℓ) ≤ (1 - α/2)^ℓ` whenever `ℓ`
iterations were completed, and `R^(ℓ+1) ≤ (1 - α/2) R^(ℓ)` whenever `ℓ + 1` were. -/
theorem lemma_3_1 {V : Type} [Fintype V] [DecidableEq V] (α εr : ℝ) (hα0 : 0 < α) (hα1 : α < 1)
    (hε0 : 0 < εr) (hε1 : εr < 1) (G : Digraph V) (s : V) (κ : ℕ) (hκ : 1 ≤ κ) (ℓ : ℕ) :
    ((fwdIter G.oracle α εr κ s ℓ).iter = ℓ →
      liveMass (fwdIter G.oracle α εr κ s ℓ) ≤ (1 - α / 2) ^ ℓ) ∧
    ((fwdIter G.oracle α εr κ s (ℓ + 1)).iter = ℓ + 1 →
      liveMass (fwdIter G.oracle α εr κ s (ℓ + 1)) ≤
        (1 - α / 2) * liveMass (fwdIter G.oracle α εr κ s ℓ)) := by sorry

end PPRInstOpt.UnknownN
