-- Prove2me | Theorems.Thm_TriFreeEst247_Main_lemma_2_1
-- name    : TriFreeEst247.Main.lemma_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:06:35.308031+00:00
-- url     : https://prove2.me/theorems/80d772b3-c952-4b23-bfdc-e96c7bbd4f39
-- title:
--   Lemma 2.1: the penalized optimum approximates distance
-- statement:
--   Let $G$ be any graph on $n\ge1$ vertices, let $0<\varepsilon<1$, and let $\lambda\ge R_\triangle(\varepsilon)$. With distance normalized by $n^2$ and $J_\lambda$ as above,
--
--   $$\mathrm{OPT}_\lambda(G)\le\operatorname{dist}(G,\mathrm{TF})\le\mathrm{OPT}_\lambda(G)+\varepsilon.$$
--
--   This compares the penalized optimum with the original distance and retains both inequalities.
--
--   Differences from the source:
--   - encoding: finite graphs and their vertex sets → simple graphs on Fin n, with unordered edges and triangles; reason: relabeling preserves every source instance and all normalized quantities
--   - encoding: λ ≥ R△(ε) → removalParameter ε ≤ ENNReal.ofReal λ; reason: the extended parameter retains infinity; the comparison forces a finite nonnegative weight at least one
-- source:
--   Asaf Shapira, Nick Kushnir, Triangle-Freeness: Estimation Is as Easy as Testing, STOC 2027 submission #247 (October 2026), source.pdf SHA-256 c24a6ad41f5c2465027e143e0aa757c3288add8cceb703078b9c0c2e18a0c3ad, p.7, Lemma 2.1

import Mathlib
import Definitions.Def_TriFreeEst247_Main_Score

open scoped ENNReal

namespace TriFreeEst247.Main

theorem lemma_2_1 {n : ℕ} (hn : 1 ≤ n) (G : Graph n) (ε lam : ℝ)
    (hε : 0 < ε ∧ ε < 1) (hlam : removalParameter ε ≤ ENNReal.ofReal lam) :
    scoreOpt G lam ≤ distance G ∧ distance G ≤ scoreOpt G lam + ε := by sorry

end TriFreeEst247.Main
