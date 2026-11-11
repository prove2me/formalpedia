-- Prove2me | Theorems.Thm_PPRInstOpt_UnknownN_lemma_3_5
-- name    : PPRInstOpt.UnknownN.lemma_3_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T17:13:50.387114+00:00
-- url     : https://prove2.me/theorems/d7487bf3-ba3d-4201-a275-de8390ff116a
-- title:
--   Lemma 3.5 — the maximum non-frozen backward residue decays by (1 − α/2) per iteration
-- statement:
--   Run Algorithm 7 (BackwardPushWithFreezing) from $t$ with budget $\kappa_b\ge1$ on a valid graph, and let $\bar r^{(\ell)}=\max_{v\notin F^{(\ell)}}r^{(\ell)}(v)$ after $\ell$ completed iterations ($0$ if every vertex is frozen). If $\ell$ iterations were completed then
--   $$\bar r^{(\ell)}\le(1-\alpha/2)^{\ell},$$
--   and if $\ell+1$ iterations were completed then $\bar r^{(\ell+1)}\le(1-\alpha/2)\bar r^{(\ell)}$.
--
--   Differences from the source:
--   - reading: max_{v∈V∖F_b^(ℓ)} r_b^(ℓ)(u) → max over v of r_b^(ℓ)(v); reason: typo: the bound variable is v
--   - reading: superscript (ℓ) = beginning of iteration ℓ, for each ℓ ≥ 0 → state after ℓ completed iterations, for ℓ up to the number of iterations Algorithm 7 performs; reason: same indexing as Lemma 3.1 (finding I4)
--   - encoding: max over V ∖ F_b → Finset.fold max 0 over non-frozen vertices; reason: residues are nonnegative; 0 only when every vertex is frozen
--   - encoding: budget κ → natural number κ ≥ 1; reason: L_f and L_b divide by κ; Algorithm 8 only uses κ = 2^i
--   - reading: εr a constant relative error → 0 < εr < 1; reason: εr ≥ 1 makes the output 0 always correct; the paper's constant-factor estimation needs εr < 1
--   - reading: candidate set {u ∈ V \ F : threshold} ∪ (C^(ℓ−1) \ F) → only vertices with positive residue are activated; reason: finding I1: with threshold 0 the printed set contains unreached vertices, not computable without n; for a positive threshold the sets coincide
--   - encoding: directed simple graph with every out-degree ≥ 1 and fixed adjacency lists → Digraph V over an arbitrary vertex type: duplicate-free out- and in-lists describing one edge set, no self-loops, nonempty out-lists; reason: same instances; list order fixes out(v, i) and in(v, i)
-- source:
--   Bertram, Jensen, Thorup, Wang, Yan, Instance-Optimality of Single-Pair Personalized PageRank, STOC 2027 submission (manuscript sha256 e1dc6b7d…), p. 22, Lemma 3.5

import Mathlib
import Definitions.Def_PPRInstOpt_UnknownN_Freezing

namespace PPRInstOpt.UnknownN

/-- Lemma 3.5 (p. 22): in every run of Algorithm 7 (any graph, target `t`, budget `κ_b ≥ 1`), with
`\bar r^(ℓ) = max_{v ∉ F^(ℓ)} r^(ℓ)(v)` after `ℓ` completed iterations:
`\bar r^(ℓ) ≤ (1 - α/2)^ℓ` whenever `ℓ` iterations were completed, and
`\bar r^(ℓ+1) ≤ (1 - α/2) \bar r^(ℓ)` whenever `ℓ + 1` were. -/
theorem lemma_3_5 {V : Type} [Fintype V] [DecidableEq V] (α εr : ℝ) (hα0 : 0 < α) (hα1 : α < 1)
    (hε0 : 0 < εr) (hε1 : εr < 1) (G : Digraph V) (t : V) (κ : ℕ) (hκ : 1 ≤ κ) (ℓ : ℕ) :
    ((bwdIter G.oracle α εr κ t ℓ).iter = ℓ →
      liveMax (bwdIter G.oracle α εr κ t ℓ) ≤ (1 - α / 2) ^ ℓ) ∧
    ((bwdIter G.oracle α εr κ t (ℓ + 1)).iter = ℓ + 1 →
      liveMax (bwdIter G.oracle α εr κ t (ℓ + 1)) ≤
        (1 - α / 2) * liveMax (bwdIter G.oracle α εr κ t ℓ)) := by sorry

end PPRInstOpt.UnknownN
