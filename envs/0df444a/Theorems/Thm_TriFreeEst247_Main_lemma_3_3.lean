-- Prove2me | Theorems.Thm_TriFreeEst247_Main_lemma_3_3
-- name    : TriFreeEst247.Main.lemma_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:11:32.442991+00:00
-- url     : https://prove2.me/theorems/ad99f460-e765-4f18-8940-394f2f5487e6
-- title:
--   Lemma 3.3: exact CSP–score identity
-- statement:
--   Let $n\ge3$, $\lambda\ge0$, and $0<\eta<1/10$. Use the labels and local functions of Definitions 3.1–3.2. The resulting $Q_G$ is a dense normalized 3-CSP: every distinct-triple local function lies in $[0,1]$ and attains one. Every labeling $\sigma:V\to A_{\lambda,\eta}$ satisfies
--
--   $$J_\lambda(D_\sigma)=(1+\lambda)(1-\operatorname{val}_{Q_G}(\sigma)).$$
--
--   The identity relates every allowed labeling to its actual deletion score, without any consistency or balance requirement on its records.
--
--   Differences from the source:
--   - encoding: finite graphs and their vertex sets → simple graphs on Fin n, with unordered edges and triangles; reason: relabeling preserves every source instance and all normalized quantities
--   - encoding: 1-based blocks and sample indices → 0-based Fin indices with modular color addition; reason: subtracting one from the block label preserves exactly the decoder and record positions
-- source:
--   Asaf Shapira, Nick Kushnir, Triangle-Freeness: Estimation Is as Easy as Testing, STOC 2027 submission #247 (October 2026), source.pdf SHA-256 c24a6ad41f5c2465027e143e0aa757c3288add8cceb703078b9c0c2e18a0c3ad, p.11, Lemma 3.3

import Mathlib
import Definitions.Def_TriFreeEst247_Main_LabelConstruction

open scoped ENNReal

namespace TriFreeEst247.Main

theorem lemma_3_3 {n : ℕ} (hn : 3 ≤ n) (G : Graph n) (lam η : ℝ)
    (hlam : 0 ≤ lam) (hη : 0 < η ∧ η < 1 / 10) :
    isDense (graphCSP G lam η) ∧
    ∀ σ : Fin n → Label lam η,
      score G lam (decodedDeletion G lam η σ) = (1 + lam) * (1 - cspValue (graphCSP G lam η) σ)
    := by sorry

end TriFreeEst247.Main
