-- Prove2me | Theorems.Thm_TriFreeEst247_Main_lemma_3_8
-- name    : TriFreeEst247.Main.lemma_3_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:16:57.452282+00:00
-- url     : https://prove2.me/theorems/99c23587-b12e-4c8e-aa8d-4e7afa8ec5a2
-- title:
--   Lemma 3.8: one sampled block update
-- statement:
--   Let $n\ge3$, $\lambda\ge0$, $0<\eta<1/10$, and use the exact $L,t_0$ from Section 3.2. Fix a coloring, a block $E_i$, and a retained edge set $H\subseteq E(G_c)$. Set $D=E(G)\setminus H$, perform the sampled update using a fresh uniform sample of $t_0$ vertices with replacement, and write $D'$ for the new deletion set. Then
--
--   $$\mathbb E[J_\lambda(D')-J_\lambda(D)]\le\frac{\lambda|E_i|}{2n^2\sqrt{t_0}}.$$
--
--   The expectation is over the fresh sample alone. Thus the bound applies after every fixed earlier history of the process.
--
--   Differences from the source:
--   - encoding: finite graphs and their vertex sets → simple graphs on Fin n, with unordered edges and triangles; reason: relabeling preserves every source instance and all normalized quantities
--   - generalization: the retained state conditioned on a prior history with the fixed balanced coloring → every coloring c and every retained set H contained in E(Gc); reason: the proof uses only block separation and the retained-set invariant, not balance, and hence includes every possible prior history
--   - encoding: conditional uniform independent sampling → the finite average over all functions Fin t₀ → Fin n with H fixed; reason: each with-replacement sample has equal probability and earlier choices are fixed
-- source:
--   Asaf Shapira, Nick Kushnir, Triangle-Freeness: Estimation Is as Easy as Testing, STOC 2027 submission #247 (October 2026), source.pdf SHA-256 c24a6ad41f5c2465027e143e0aa757c3288add8cceb703078b9c0c2e18a0c3ad, p.13, Lemma 3.8

import Mathlib
import Definitions.Def_TriFreeEst247_Main_BlockUpdates

open scoped ENNReal

namespace TriFreeEst247.Main

theorem lemma_3_8 {n : ℕ} (hn : 3 ≤ n) (G : Graph n) (lam η : ℝ)
    (hlam : 0 ≤ lam) (hη : 0 < η ∧ η < 1 / 10)
    (c : Fin n → Fin (colorCount η)) (i : Fin (colorCount η))
    (H : EdgeSet n) (hH : H ⊆ coloredEdges G c) :
    expectedIncrease (t := sampleCount lam η) G lam c i H ≤
      lam * ((edgeBlock G c i).card : ℝ) /
        (2 * (n : ℝ)^2 * Real.sqrt (sampleCount lam η : ℝ)) := by sorry

end TriFreeEst247.Main
