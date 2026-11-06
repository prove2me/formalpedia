-- Prove2me | Theorems.Thm_PottsRapidMixing_theorem_1_1
-- name    : PottsRapidMixing.theorem_1_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:53:30.817103+00:00
-- url     : https://prove2.me/theorems/4d8cefea-7435-495b-91f0-381536c6d847
-- title:
--   Theorem 1.1, p.2 — Potts Glauber dynamics mixes in $O(n(\log n)^\kappa)$ steps throughout uniqueness
-- statement:
--   Fix integers $\Delta\ge3$ and $q\ge2$, and let $0<\beta<\beta_u(q,\mathbb T_\Delta)$. There are constants $\kappa=\kappa(\Delta,q,\beta)>0$ and $C>0$ such that with probability $1-o(1)$, the $q$-state Potts Glauber dynamics at inverse temperature $\beta$ on a uniformly random $\Delta$-regular graph $G$ on $n$ vertices has
--   $$t_{\mathrm{mix}}\le C\,n(\log n)^\kappa,\qquad t_{\mathrm{mix}}=\min\Bigl\{t\ge0:\max_{\sigma}\|P^t(\sigma,\cdot)-\mu\|_{\mathrm{TV}}\le\tfrac14\Bigr\}.$$
--
--   This resolves whether the simplest Markov chain for the Potts model is fast throughout the uniqueness regime on almost every regular graph. The statement is unconditional: it has no hypothesis on the graph.
--
--   **Formalization Note** The chain is `MarkovMixing.glauber` of the Potts law, whose rows are the heat-bath update of p.1 since the Potts law has full support.
--
--   Differences from the source:
--   - encoding: with probability 1 − o(1) over a uniformly random Δ-regular graph on n vertices → the fraction of Δ-regular graphs on Fin n with the property tends to 1 along n with nΔ even; reason: the uniform law exists exactly for nΔ even and n > Δ; same statement
--   - reading: constants named in a "with probability 1 − o(1)" statement → the constants are quantified before n and the graph event; reason: the stronger reading, and what the proof gives: every constant is fixed first, then G is taken in the event
--   - encoding: t_mix = O(n(log n)^κ) → d(⌊C n (log n)^κ⌋) ≤ 1/4 with d = distStationary; reason: d(t) is nonincreasing, so this says t_mix ≤ ⌊C n (log n)^κ⌋; it avoids the junk value of a natural-number sInf (paper.md R3)
-- source:
--   Blanca, Gheissari, Park, Zhang, Rapid mixing of Potts Glauber dynamics throughout uniqueness, arXiv:2610.42059, Theorem 1.1, p.2

import Mathlib
import Definitions.Def_mm_mixing
import Definitions.Def_mm_mcmc
import Definitions.Def_PottsRapidMixing_Ensemble
import Definitions.Def_PottsRapidMixing_Threshold
import Definitions.Def_PottsRapidMixing_PottsLaw

open scoped Classical
open Filter Topology

namespace PottsRapidMixing

/-- **Theorem 1.1** (Blanca, Gheissari, Park, Zhang, arXiv:2610.42059, p.2). Fix integers `Δ ≥ 3`,
`q ≥ 2` and `0 < β < β_u(q, T_Δ)`. With probability `1 − o(1)`, the `q`-state Potts Glauber dynamics at
inverse temperature `β` on a uniformly random Δ-regular graph on `n` vertices has mixing time
`O(n (log n)^κ)`, for a constant `κ = κ(Δ, q, β) > 0`.

**Formalization Note.** `κ` and the `O`-constant `C` are fixed before `n` (the paper's proof fixes them
first, then takes `G` in an event of probability `1 − o(1)`). `t_mix ≤ T` is stated as `d(⌊T⌋) ≤ 1/4`, with
`d = distStationary`: `d` is nonincreasing, and this form has none of the junk of a natural-number
`sInf`. The uniform law lives on `n` with `nΔ` even. -/
theorem theorem_1_1 (Δ q : ℕ) (hΔ : 3 ≤ Δ) (hq : 2 ≤ q) (β : ℝ) (hβ : 0 < β)
    (hβu : β < betaU (q : ℝ) Δ) :
    ∃ κ C : ℝ, 0 < κ ∧ 0 < C ∧ WithHighProb Δ (fun n G =>
      MarkovMixing.distStationary (MarkovMixing.glauber (pottsLaw G β q)) (pottsLaw G β q)
        ⌊C * (n : ℝ) * Real.log (n : ℝ) ^ κ⌋₊ ≤ 1 / 4) := by sorry

end PottsRapidMixing
