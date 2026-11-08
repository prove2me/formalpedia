-- Prove2me | Theorems.Thm_PoSUndirected_lemma_A_7_block_transfer
-- name    : PoSUndirected.lemma_A_7_block_transfer
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T08:00:24.484794+00:00
-- url     : https://prove2.me/theorems/41047798-5e45-4ad6-a72a-ab955e6f71d4
-- title:
--   Lemma A.7 — block transfer at every height
-- statement:
--   Consider the host of any finite depth $d$ at $\eta(t)$, $0\le t<1$ rational, and a weak equilibrium $A$. For every block $b$:
--
--   1. all immediate floor owners and chord owners of $b$ are confined;
--   2. if $b$ has no external users, its chord owners are direct;
--   3. if $b$ has $q\ge1$ external users, each pays more than the ceiling cost of $b$ divided by $q$ inside the block region.
--
--   This is the height induction combining floor confinement, chord confinement (an escaping chord owner is charged more than $\rho/7$ by the six other gadgets) and the local comparison.
--
--   Differences from the source:
--   - encoding: "Assume the local comparison and equation (2)" → the parameters are $\eta(t)$ with $0\le t<1$ rational; reason: both the local comparison (Lemma A.2) and equation (2) hold there and are milestones of this mission
--   - encoding: "at every finite block height" → every block of the depth-$d$ host, for every $d$; reason: height $=d-$depth
-- source:
--   Tsoufis, The Price of Stability in Undirected Network Design: Lower Bounds and Structural Guarantees (preprint, sha256 c095d811fa04b471d74ba4fdab8fb89ccb3d34079d3bf07384f46ac57144866c), Lemma A.7, p.16 (PDF p.18)

import Mathlib
import Definitions.Def_PoSUndirected_gadgetRegion

open CongestionPoA.AsymSum PriceOfStability.Harmonic

namespace PoSUndirected

/-- Tsoufis (preprint, sha256 c095d811…), Lemma A.7 (Block transfer), p.16 (PDF p.18). In the
construction at `η(t)`, `0 ≤ t < 1` rational (where the local comparison, Lemma A.2, and equation
(2) hold), of any finite depth `d`, in every weak equilibrium `A` and for every block `b` (every
finite height): all immediate floor and chord owners of `b` are confined; if `b` has no external
users, its chord owners are direct; if it has `q ≥ 1` external users, each pays more than the
ceiling cost of `b` divided by `q` inside the block region.

**Formalization Note.** "Assume the local comparison and equation (2)" is discharged by fixing the
parameters to `η(t)` with `0 ≤ t < 1`, where both are milestones of this mission; neither is a
hypothesis here. -/
theorem lemma_A_7_block_transfer (t : ℚ) (ht0 : 0 ≤ t) (ht1 : t < 1) (d : ℕ)
    (A : HEdge d → Finset (HEdge d)) (hA : IsPureNash (hostGame (etaAt t) d) A) (b : HBlock d) :
    OwnersConfined A b ∧
    ((extUsers A (blockRegion b)).card = 0 →
      ∀ g κ, A (HEdge.chord b.1 b.2 g κ) = {HEdge.chord b.1 b.2 g κ}) ∧
    CrossBound (etaAt t) A b := by sorry

end PoSUndirected
