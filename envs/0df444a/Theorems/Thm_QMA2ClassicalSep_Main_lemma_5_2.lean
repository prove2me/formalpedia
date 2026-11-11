-- Prove2me | Theorems.Thm_QMA2ClassicalSep_Main_lemma_5_2
-- name    : QMA2ClassicalSep.Main.lemma_5_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T21:02:59.929793+00:00
-- url     : https://prove2.me/theorems/9e5d48f0-42ad-45a1-b0df-c226f71127b4
-- title:
--   Lemma 5.2 — class sizes: $\Pr_\theta[\theta\notin\Theta_{\mathrm{size}}]\le4K e^{-\varepsilon_0^2\mu/3}$ and blocks of size $\ge(1-\varepsilon_0)^2\mu^2$
-- statement:
--   Let $k\ge2$, $N=2^k$, $K=N^2$, $\mu=N$, $\varepsilon_0=1/40$, and let $\theta=(c_A,c_B)$ be the uniformly random pair-labeling of the NO construction. Then
--
--   $$
--   \Pr_\theta[\theta\notin\Theta_{\mathrm{size}}]\le4K\exp(-\varepsilon_0^2\mu/3),
--   $$
--
--   and for every $\theta\in\Theta_{\mathrm{size}}$, every nonempty block of its partition has size at least $(1-\varepsilon_0)^2\mu^2$.
--
--   The first bound makes the class-size condition hold with overwhelming probability; the second gives the domain-size lower bound $s_-$ used for the compressed NO records.
--
--   Differences from the source:
--   - encoding: Pr over the labeling sampled in the NO construction; every nonempty block → ratio of counts over all labelings; the block of every vertex; reason: θ is uniform on a finite set; every nonempty block is the block of each of its vertices
-- source:
--   Sabee Grewal, Saachi Mutreja, Kabir Tomer, A classical oracle separation between QMA and QMA(2), STOC 2027 submission #618 (October 2026), SHA-256 79883d9d08b98b41b1bb600a6644f3f578ecb803702383a9f2a58d5bc7dacedf, p. 21, Lemma 5.2

import Definitions.Def_QMA2ClassicalSep_Main_HardDist

namespace QMA2ClassicalSep.Main

theorem lemma_5_2 (k : ℕ) (hk : 2 ≤ k) :
    probLabeling (k := k) (fun θ => ¬ InThetaSize θ) ≤
        4 * KK k * Real.exp (-(eps0 ^ 2 * mu k) / 3) ∧
      ∀ θ : Labeling k, InThetaSize θ → ∀ x : HVtx k,
        (1 - eps0) ^ 2 * mu k ^ 2 ≤ ((blockOf θ x).card : ℝ) := by sorry

end QMA2ClassicalSep.Main
