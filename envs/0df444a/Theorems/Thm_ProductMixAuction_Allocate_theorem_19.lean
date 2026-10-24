-- Prove2me | Theorems.Thm_ProductMixAuction_Allocate_theorem_19
-- name    : ProductMixAuction.Allocate.theorem_19
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T04:39:08.460253+00:00
-- url     : https://prove2.me/theorems/8eb9e9bd-9c90-4081-aaeb-6ceae2cb7c00
-- title:
--   Theorem 19, p. 23 — ALLOCATE splits t into bundles demanded at p within |J|·C(n+1,2) iterations, with genuine SFM calls
-- statement:
--   Let $J$ be a finite set of bidders, each with a valid list $\mathcal B^j$ of integral bids with weights $\pm1$, let $p\in\mathbb Z^n$ be an integral price and $t\in\mathbb Z^n$ a target bundle demanded at $p$ by the aggregate list, $t\in D_{\mathcal B}(p)$. Run ALLOCATE (Algorithm 1) from the initial allocation problem, with any parameter selector meeting the output contract of FindParams (Lemma 10) and any SFM oracle that returns a minimiser of every submodular set function. Then there is $k$ with
--   $$k\le|J|\binom{n+1}{2}$$
--   such that after $k$ iterations of the main loop:
--
--   1. every bid list is empty, so the algorithm stops;
--   2. every ShiftProjectUnshift call among these iterations passes submodular set functions to the oracle;
--   3. the returned partial allocations $m^j$, restricted to the goods $[n]$, partition the target: $\sum_{j\in J}m^j=t$ and $m^j\in D_{\mathcal B^j}(p)$ for every $j$.
--
--   So ALLOCATE solves the allocation problem of §2.5 with at most $|J|\binom{n+1}2$ iterations, each consisting of one FindParams call, at most one ShiftProjectUnshift with two submodular minimisations, and two linear-time procedures; this is the iteration count behind the bound $O(n^2|J|(\alpha(n)n|\mathcal B|+T(n)))$.
--
--   Differences from the source:
--   - generalization: FindParams (Algorithm 2), a subroutine 'not fully specified' (p. 23) → every selector that, on problems with only marginal bids and a non-empty list, returns a demand cluster with at most one link good or a cycle-link good with an incident cycle label; reason: every walk FindParams may take yields such outputs by Lemma 10, and so does PriorityParams (Algorithm 6); the claim for FindParams is the special case
--   - encoding: in time O(n²|J|(α(n)n|ℬ| + T(n))), T(n) the time to minimise an n-dimensional submodular set function → at most |J|·C(n+1,2) loop iterations, each with one selector call and at most one ShiftProjectUnshift whose two oracle calls are on submodular functions; reason: no machine model is formalized; this is how the proof (p. 23) counts: |J|·C(n+1,2) iterations, per-iteration costs α(n)n|ℬ| for FindParams and T(n) per SFM call
--   - reading: an SFM algorithm (cost T(n)) → any oracle returning a minimiser of every submodular input, unconstrained on other inputs; reason: the paper uses SFM as a black box on submodular inputs; clause 2 states that every call is on such an input
--   - encoding: bundles in ℤⁿ; allocation problems carry a reject coordinate → the run works over [n]₀; the conclusion drops coordinate 0 (Fin.tail); reason: the target and the output of §2.5 are bundles of the goods [n]
-- source:
--   Baldwin, Goldberg, Klemperer, Lock, Solving Strong-Substitutes Product-Mix Auctions, arXiv:1909.07313v3, p. 23, Theorem 19, Algorithm 1; allocation problem p. 11

import Mathlib
import Definitions.Def_ProductMixAuction_Allocate_Algorithm

namespace ProductMixAuction.Allocate

theorem theorem_19 {n : ℕ} {J : Type*} [Fintype J] [DecidableEq J]
    (B : J → List (IntBid n)) (hw : ∀ j, ∀ b ∈ B j, b.w = 1 ∨ b.w = -1)
    (hvalid : ∀ j, Valid ((B j).map IntBid.toBid))
    (p t : Fin n → ℤ)
    (hclear : t ∈ demandN (aggregate fun j => (B j).map IntBid.toBid) (fun i => (p i : ℝ)))
    (sel : Selector n J) (hsel : sel.Admissible)
    (sfm : SFMOracle n) (hsfm : SfmAdmissible sfm) :
    ∃ k ≤ Fintype.card J * (n + 1).choose 2,
      (∀ j, (run sel sfm (initial B p t) k).B j = []) ∧
      (∀ k' < k, StepGenuine sel (run sel sfm (initial B p t) k')) ∧
      ∑ j, Fin.tail ((run sel sfm (initial B p t) k).m j) = t ∧
      ∀ j, Fin.tail ((run sel sfm (initial B p t) k).m j) ∈
        demandN ((B j).map IntBid.toBid) (fun i => (p i : ℝ)) := by sorry

end ProductMixAuction.Allocate
