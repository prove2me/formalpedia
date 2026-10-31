-- Prove2me | Theorems.Thm_SplitPMSGame_core_properties
-- name    : SplitPMSGame.core_properties
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:12:13.125677+00:00
-- url     : https://prove2.me/theorems/46010c3f-0b3c-4e89-84ac-77c9ecd0aed8
-- title:
--   Core properties (i)–(ii) — covariance and superadditivity of the core (corrected: (i) reads $\mathbb C(M,\alpha G)=\alpha\,\mathbb C(M,G)$)
-- statement:
--   Let $M$ be a finite set of players and $G_1,G_2:2^M\to\mathbb R$ cost games, with $\mathbb C(M,G)$ the (possibly empty) core.
--
--   1. **Covariance under strategic equivalence:** for every $\alpha>0$, $\mathbb C(M,\alpha G_1)=\alpha\,\mathbb C(M,G_1)$.
--   2. **Superadditivity:** $\mathbb C(M,G_1)+\mathbb C(M,G_2)\subseteq\mathbb C(M,G_1+G_2)$.
--
--   Sums and multiples of games and of sets of allocations are taken pointwise. Combined with Theorem 1, these properties let core allocations of the CB games be added up to a core allocation of the PMS game.
--
--   Differences from the source:
--   - correction: (i): if G₂ = αG₁ for α > 0, then ℂ(M, G₁) = αℂ(M, G₂) → coreSet (α • G₁) = α • coreSet G₁, i.e. ℂ(M, G₂) = αℂ(M, G₁); reason: the printed identity is false for α ≠ 1: M = {1}, G₁({1}) = 1, α = 2 gives ℂ(M, G₁) = {1} but αℂ(M, G₂) = {4}; the corrected form is Peleg–Sudhölter's covariance
--   - generalization: cooperative games, with G(∅) = 0 → any set functions G₁, G₂ : Finset M → ℝ; reason: games with G(∅) = 0 are a special case; both properties hold for every set function
--   - encoding: ℂ(M, G₁) + ℂ(M, G₂) and αℂ(M, G) → pointwise Set addition and scalar multiplication; reason: Lean convention; same sets
-- source:
--   Alon, Anily, The Basic Core of a Parallel Machines Scheduling Game, MSOM 25(6) (2023), doi:10.1287/msom.2021.0337, §5.1.1, p.2242 (PDF p.11), properties (i)–(ii), citing Peleg–Sudhölter (2007), pp.19–21

import Mathlib
import Definitions.Def_SplitPMSGame_IsCoreAlloc

namespace SplitPMSGame

open Pointwise

/-- **Core properties (i)–(ii)** (Alon, Anily, *The Basic Core of a Parallel Machines Scheduling
Game*, MSOM 25(6) (2023), §5.1.1, p.2242, citing Peleg–Sudhölter 2007, pp.19–21). For a finite
player set `M` and cost games `G₁, G₂ : 2^M → ℝ`:
(i) covariance under strategic equivalence: for `α > 0`, `ℂ(M, αG₁) = α ℂ(M, G₁)`;
(ii) superadditivity: `ℂ(M, G₁) + ℂ(M, G₂) ⊆ ℂ(M, G₁ + G₂)`.

**Formalization Note** The printed (i) reads "if `G₂ = αG₁`, for `α > 0`, then
`ℂ(M, G₁) = αℂ(M, G₂)`", which is false for `α ≠ 1` (`M = {1}`, `G₁({1}) = 1`, `α = 2`:
`ℂ(M, G₁) = {1}`, `αℂ(M, G₂) = {4}`); the statement here is the corrected
`ℂ(M, G₂) = αℂ(M, G₁)`. Sums and scalar multiples of games and of sets of allocations are
pointwise. -/
theorem core_properties {M : Type*} [Fintype M] (G₁ G₂ : Finset M → ℝ) :
    (∀ α : ℝ, 0 < α → coreSet (α • G₁) = α • coreSet G₁) ∧
      coreSet G₁ + coreSet G₂ ⊆ coreSet (G₁ + G₂) := by sorry

end SplitPMSGame
