-- Prove2me | Theorems.Thm_RandOnlineSetCover_InfoLB_observation_3_2
-- name    : RandOnlineSetCover.InfoLB.observation_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:40:48.477589+00:00
-- url     : https://prove2.me/theorems/8d3e8a79-e202-4bd5-ae2d-628c215c491d
-- title:
--   Observation 3.2 — the inner optimum is at most 2k
-- statement:
--   Let $k\ge1$, let $T$ be the complete binary tree with $2k$ levels, and color its vertices with any $m$ colors. Form the inner request sequence $I_{\chi,\pi}$ along a root-to-leaf path $\pi$, using any fixed enumeration in each batch. Then every path satisfies
--
--   $$
--   \operatorname{Opt}(I_{\chi,\pi})\le2k.
--   $$
--
--   This supplies a pointwise offline upper bound for the distribution of inner instances; consequently the bound holds with probability one for the uniformly selected path.
--
--   Differences from the source:
--   - generalization: the construction sets m = 512k² and fixes canonical batch orders → arbitrary m, every coloring, and every fixed per-vertex enumeration; reason: the cover bound uses neither the palette size nor the within-batch order, and specializes to the source construction
--   - encoding: probability-one bound on the uniform path experiment → the bound for every path, with the raw optimum in extended naturals; reason: the uniform finite distribution gives positive mass to every path; the extended value prevents an invalid raw request from receiving optimum zero
-- source:
--   Roie Levin, STOC 2027 submission #400 (October 2026), Observation 3.2, p. 4. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/400.pdf

import Mathlib
import Definitions.Def_RandOnlineSetCover_InfoLB_Inner

namespace RandOnlineSetCover.InfoLB

theorem observation_3_2 (k m : ℕ) (hk : 0 < k) (O : BatchOrder k)
    (χ : BinaryVertex (2 * k) → Fin m) (π : InnerPath k) :
    listOpt (innerRequests O χ π) ≤ (2 * k : ℕ) := by sorry

end RandOnlineSetCover.InfoLB
