-- Prove2me | Theorems.Thm_SplayDynOpt_lemma_26
-- name    : SplayDynOpt.lemma_26
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T15:57:52.029798+00:00
-- url     : https://prove2.me/theorems/1e5c2b8d-ebc6-497a-958d-1c2e2972c355
-- title:
--   Lemma 26 — the interface's total activity bound
-- statement:
--   For all $C_{\mathrm{growing}},C_{\mathrm{exempt}}\in\mathbb N$ and $\gamma\in(0,1/2]$ there is a constant $K$ such that for every $G\ge2$, every finite set $V$ and every valid run of the interface from an initial state, the total activity $A$, the sum of matching sizes $|M|$ over all Pass operations, satisfies
--   $$
--   A\le K\,G\cdot\#\mathrm{Insert}+K\log_2 G\cdot\#\mathrm{ValueChange}.
--   $$
--
--   The bound abstracts the amortized analysis of pure and multi-pass pairing heaps, and it bounds the internal pairings of the lazy intervals.
--
--   Differences from the source:
--   - reading: A ≤ #Insert · O(G) + #ValueChange · O(log G), with C_growing, C_exempt ∈ O(1), γ ∈ [1/O(1), 1/2] → one K for both terms, depending on C_growing, C_exempt, γ only, chosen before G, V and the run; reason: one K serves both O(·) terms by taking the maximum; K(γ₀) also serves every γ ≥ γ₀
--   - encoding: blocks B ∈ 𝓑, a matching M as a set, integer constants → blocks indexed by creation order, M a list without repeated elements, natural-number constants; reason: losers enter distinct blocks so order is irrelevant; a negative constant behaves like 0
-- source:
--   Chmel et al., Splay trees are almost dynamically optimal, arXiv:2607.18498 (version of 2026-11-02, sha256 6881e83c…), Lemma 26, p.39 (proof pp.40–43); interface §5.5.1, pp.38–39

import Mathlib
import Definitions.Def_SplayDynOpt_RunValid

set_option autoImplicit false

namespace SplayDynOpt

/-- **Lemma 26 (interface abstraction of pairing-heap analysis).** For all constants
`C_growing, C_exempt` and `γ ∈ (0, 1/2]` there is `K` such that for every `G ≥ 2`, every finite set of
elements `V` and every valid sequence of interface operations from an initial state, the total
activity satisfies `A ≤ K·G·#Insert + K·log₂ G·#ValueChange`.

Chmel, Haeupler, Hladík, Koucký, Roeyskoe, Rozhoň, Sladký, Tarjan, *Splay trees are almost
dynamically optimal*, arXiv:2607.18498 (version of 2026-11-02, sha256 6881e83c…), Lemma 26, p.39 (proof pp.40–43); interface §5.5.1, pp.38–39.

**Formalization Note.** One constant `K` serves both `O(·)` terms; it depends on
`C_growing, C_exempt, γ` only (not on `G`, `V` or the operations). The integer constants are natural
numbers (a negative constant behaves like `0`). -/
theorem lemma_26 :
    ∀ Cg Ce : ℕ, ∀ γ : ℝ, 0 < γ → γ ≤ 1 / 2 → ∃ K : ℝ, ∀ G : ℕ, 2 ≤ G →
      ∀ (V : Type) [Fintype V] [DecidableEq V] (s₀ : IState V) (ops : List (IOp V)),
        s₀.IsInitial ⟨Cg, Ce, G, γ⟩ → RunValid ⟨Cg, Ce, G, γ⟩ s₀ ops →
          (activity ops : ℝ) ≤ K * G * numInsert ops + K * Real.logb 2 G * numValueChange ops := by sorry

end SplayDynOpt
