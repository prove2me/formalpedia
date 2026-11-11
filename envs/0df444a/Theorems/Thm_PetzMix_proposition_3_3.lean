-- Prove2me | Theorems.Thm_PetzMix_proposition_3_3
-- name    : PetzMix.proposition_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-11T04:14:56.487476+00:00
-- url     : https://prove2.me/theorems/29c6f164-744e-4c2d-9c37-db55f2537871
-- title:
--   Proposition 3.3 — counting cyclic blocks
-- statement:
--   Let $1\le\ell<n$ and fix a site $i\in\Lambda_n$.
--
--   1. Exactly $\ell$ blocks in $\mathcal B_{n,\ell}$ contain $i$.
--   2. For every $r\ge1$, at most two blocks $B\in\mathcal B_{n,\ell}$ satisfy $i\notin B$ and $\operatorname{dist}(i,B)=r$.
--   3. Consequently, for every $\eta:\mathbb N\to[0,\infty)$ with $\sum_{r\ge1}\eta(r)<\infty$,
--   $$
--   \sum_{B\in\mathcal B_{n,\ell},\ i\notin B}\eta\big(\operatorname{dist}(i,B)\big)\le a_\eta=2\sum_{r=1}^\infty\eta(r).
--   $$
--
--   This is the one-dimensional counting behind the balance "erasure at rate one versus influence at rate $a_\eta/\ell$".
--
--   **Formalization Note** Blocks are counted by their left ends $s\in\Lambda_n$.
--
--   Differences from the source:
--   - encoding: B ∈ B_{n,ℓ}, the cyclic intervals of length ℓ, with 1 ≤ ℓ < n → cycBlock ℓ s for s : Fin n, 1 ≤ ℓ < n; reason: the n blocks are indexed by their left ends and are distinct for 1 ≤ ℓ < n
--   - encoding: a summable decay function, a_η = 2Σ_{r≥1} η(r) < ∞ → Summable (fun r => η (r + 1)) with aEta η = 2 * ∑' r, η (r + 1); reason: a real tsum of a divergent series is 0, so convergence is stated explicitly
-- source:
--   Kim, Rapid mixing of quantum spin chains at any finite temperature, arXiv:2610.01190 (held copy sha256 38ff48d0…), Proposition 3.3, (45), p.17

import Mathlib
import Definitions.Def_PetzMix_HasExtInfluence

open scoped Matrix ComplexOrder ENNReal

set_option autoImplicit false

namespace PetzMix

open QDSGibbs

/-- **Proposition 3.3 (Counting cyclic blocks)** (Kim, Rapid mixing of quantum spin chains at any finite temperature, arXiv:2610.01190 (held copy sha256 38ff48d0…), Proposition 3.3, (45), p.17). Fix
`1 ≤ ℓ < n` and a site `i`. Exactly `ℓ` blocks in `B_{n,ℓ}` contain `i`. For every `r ≥ 1`, at most
two blocks `B ∈ B_{n,ℓ}` satisfy `i ∉ B` and `dist(i, B) = r`. Consequently, for every nonnegative
summable `η`, `Σ_{B ∈ B_{n,ℓ}, i ∉ B} η(dist(i, B)) ≤ a_η`.

**Formalization Note** The `n` blocks are counted by their left ends `s : Fin n` (they are distinct
for `1 ≤ ℓ < n`). `a_η = 2 Σ_{r ≥ 1} η(r)` is `aEta η`, used with explicit summability. -/
theorem proposition_3_3 (n ℓ : ℕ) (hℓ : 1 ≤ ℓ) (hℓn : ℓ < n) (i : Fin n) :
    (Finset.univ.filter (fun s : Fin n => i ∈ cycBlock ℓ s)).card = ℓ ∧
    (∀ r : ℕ, 1 ≤ r →
      (Finset.univ.filter (fun s : Fin n => i ∉ cycBlock ℓ s ∧ setDist i (cycBlock ℓ s) = r)).card ≤ 2) ∧
    (∀ η : ℕ → ℝ, (∀ r, 0 ≤ η r) → Summable (fun r => η (r + 1)) →
      ∑ s ∈ Finset.univ.filter (fun s : Fin n => i ∉ cycBlock ℓ s), η (setDist i (cycBlock ℓ s)) ≤
        aEta η) := by sorry

end PetzMix
