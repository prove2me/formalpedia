-- Prove2me | Theorems.Thm_TriFreeEst247_Main_lemma_3_9
-- name    : TriFreeEst247.Main.lemma_3_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:15:55.806126+00:00
-- url     : https://prove2.me/theorems/a59f5cd8-b677-45dd-83a9-3e127cdb2548
-- title:
--   Lemma 3.9: a good choice of samples exists
-- statement:
--   Fix $n\ge3$, $\lambda\ge0$, $0<\eta<1/10$, any balanced coloring $c$, and any deletion set $D^*$ minimizing $J_\lambda$ over $E(G)$. Start from $D_0=D^*\cup B_c$ and perform Definitions 3.6–3.7 with the exact $L$ blocks and sample size $t_0$. There is a choice of all samples such that
--
--   $$J_\lambda(D_L)\le\mathrm{OPT}_\lambda(G)+\eta/2.$$
--
--   This existence assertion holds for every such coloring and minimizer.
--
--   Differences from the source:
--   - encoding: finite graphs and their vertex sets → simple graphs on Fin n, with unordered edges and triangles; reason: relabeling preserves every source instance and all normalized quantities
--   - encoding: L stages, each with t₀ ordered sampled vertices → a function Fin L → Fin t₀ → Fin n and a zero-based state recursion; reason: this encodes exactly every possible execution, without changing its initial set or update rule
-- source:
--   Asaf Shapira, Nick Kushnir, Triangle-Freeness: Estimation Is as Easy as Testing, STOC 2027 submission #247 (October 2026), source.pdf SHA-256 c24a6ad41f5c2465027e143e0aa757c3288add8cceb703078b9c0c2e18a0c3ad, p.14, Lemma 3.9

import Mathlib
import Definitions.Def_TriFreeEst247_Main_BlockUpdates

open scoped ENNReal

namespace TriFreeEst247.Main

theorem lemma_3_9 {n : ℕ} (hn : 3 ≤ n) (G : Graph n) (lam η : ℝ)
    (hlam : 0 ≤ lam) (hη : 0 < η ∧ η < 1 / 10)
    (c : Fin n → Fin (colorCount η)) (hc : balanced c)
    (Dstar : EdgeSet n) (hD : Dstar ⊆ edges G) (hopt : score G lam Dstar = scoreOpt G lam) :
    ∃ u : Fin (colorCount η) → Fin (sampleCount lam η) → Fin n,
      score G lam (finalDeletion G lam η c Dstar u) ≤ scoreOpt G lam + η / 2 := by sorry

end TriFreeEst247.Main
