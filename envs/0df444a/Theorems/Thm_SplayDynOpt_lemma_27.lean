-- Prove2me | Theorems.Thm_SplayDynOpt_lemma_27
-- name    : SplayDynOpt.lemma_27
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T15:57:40.605497+00:00
-- url     : https://prove2.me/theorems/d92fcb1c-50f6-421f-ba0a-9666e6ab08c0
-- title:
--   Lemma 27 — insignificant passes contribute at most a $1/(4G)$ fraction
-- statement:
--   For all $C_{\mathrm{growing}},C_{\mathrm{exempt}}\in\mathbb N$ and $\gamma\in(0,1/2]$ there is a constant $K$ such that for every $G\ge2$ there is a threshold $\tau\le K\log_2 G$ with the following property. Call a Pass on a block **significant** if the pass count of the block was strictly less than $\tau$ before the Pass, and **insignificant** otherwise. For every finite set $V$ and every valid run of the interface from an initial state,
--   $$
--   A_{\mathrm{insig}}\le\frac{1}{4G}\bigl(A+\#\mathrm{Insert}\bigr).
--   $$
--
--   This lets the analysis ignore the activity on blocks with a high pass count.
--
--   Differences from the source:
--   - reading: τ = O(log G), C_growing, C_exempt ∈ O(1), γ ∈ [1/O(1), 1/2], for any sequence of operations → K depends on C_growing, C_exempt, γ only, and τ is chosen before V and the run; reason: K(γ₀) also serves every γ ≥ γ₀, since a run valid for γ is valid for γ₀, so dependence on γ matches dependence on its lower bound
--   - encoding: blocks B ∈ 𝓑, a matching M as a set, integer constants → blocks indexed by creation order, M a list without repeated elements, natural-number constants; reason: losers enter distinct blocks so order is irrelevant; a negative constant behaves like 0
-- source:
--   Chmel et al., Splay trees are almost dynamically optimal, arXiv:2607.18498 (version of 2026-11-02, sha256 6881e83c…), Lemma 27, p.39 (proof p.43); interface §5.5.1, pp.38–39

import Mathlib
import Definitions.Def_SplayDynOpt_RunValid

set_option autoImplicit false

namespace SplayDynOpt

/-- **Lemma 27.** For all constants `C_growing, C_exempt` and `γ ∈ (0, 1/2]` there is `K` such that for
every `G ≥ 2` there is a threshold `τ ≤ K · log₂ G` with the following property: for every finite
set of elements `V` and every valid sequence of interface operations from an initial state,
`A_insig ≤ (A + #Insert) / (4G)`, where `A_insig` is the total matching size of the insignificant
passes (pass count `≥ τ` before the pass) and `A` that of all passes.

Chmel, Haeupler, Hladík, Koucký, Roeyskoe, Rozhoň, Sladký, Tarjan, *Splay trees are almost
dynamically optimal*, arXiv:2607.18498 (version of 2026-11-02, sha256 6881e83c…), Lemma 27, p.39 (proof p.43); interface §5.5.1, pp.38–39.

**Formalization Note.** "`τ = O(log G)`" with "`C_growing, C_exempt ∈ O(1)`" and "`γ ∈ [1/O(1), 1/2]`" is
read as: `K` depends on `C_growing, C_exempt, γ` only, and `τ` is chosen before the elements and the
operations. The integer constants are natural numbers (a negative constant behaves like `0`). -/
theorem lemma_27 :
    ∀ Cg Ce : ℕ, ∀ γ : ℝ, 0 < γ → γ ≤ 1 / 2 → ∃ K : ℝ, ∀ G : ℕ, 2 ≤ G →
      ∃ τ : ℕ, (τ : ℝ) ≤ K * Real.logb 2 G ∧
        ∀ (V : Type) [Fintype V] [DecidableEq V] (s₀ : IState V) (ops : List (IOp V)),
          s₀.IsInitial ⟨Cg, Ce, G, γ⟩ → RunValid ⟨Cg, Ce, G, γ⟩ s₀ ops →
            (insigActivity τ s₀ ops : ℝ) ≤ ((activity ops : ℝ) + numInsert ops) / (4 * G) := by sorry

end SplayDynOpt
