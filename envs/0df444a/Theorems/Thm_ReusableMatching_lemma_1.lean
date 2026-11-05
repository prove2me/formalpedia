-- Prove2me | Theorems.Thm_ReusableMatching_lemma_1
-- name    : ReusableMatching.lemma_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T05:32:08.503881+00:00
-- url     : https://prove2.me/theorems/d1d7c8ed-bc43-4801-b4b1-abaf510e9306
-- title:
--   Lemma 1: reverse weak duality and $\Gamma$-approximate dual feasibility give $\mathrm{OPT}\le P/\Gamma$
-- statement:
--   Let an OBMRR instance be given, let $P\in\mathbb R$, and let $\alpha_{i,t}\ge0$ ($i\in V$, $t$ an arrival) and $\beta_j\ge0$ ($j$ an arrival) be a dual assignment with objective value
--
--   $$
--   D=\sum_{i\in V}\sum_{t}\alpha_{i,t}+\sum_j\beta_j .
--   $$
--
--   Suppose that, for some $\Gamma\in(0,1]$,
--
--   1. (reverse weak duality) $P\ge D$;
--   2. (approximate dual feasibility) for every edge $(i,j)\in E$,
--   $$
--   \beta_j+\sum_{t=\max\{j-d+1,1\}}^{j}\alpha_{i,t}\ \ge\ \Gamma\, r_i .
--   $$
--
--   Then
--
--   $$
--   P\ \ge\ \Gamma\cdot\mathrm{OPT}.
--   $$
--
--   In the paper, $P$ is the expected reward of an online algorithm, so the conclusion says that the algorithm is $\Gamma$-competitive. This lemma is the frame of the analysis of Periodic Reranking: Lemmas 2 and 3 supply its two hypotheses.
--
--   Differences from the source:
--   - generalization: P is the objective value of the primal assignment of an online algorithm → P is an arbitrary real number; reason: the proof uses only P ≥ D; taking P equal to the algorithm's expected reward gives the paper's statement
--   - reading: a dual assignment {α_{i,t}, β_j} of (D) → α_{i,t} ≥ 0 and β_j ≥ 0 as hypotheses; reason: the sign constraints are part of (D), and the proof (p.33) uses that {α/Γ, β/Γ} is a feasible dual assignment; without them the lemma is false (an α_{i,t} on a non-edge can be made arbitrarily negative)
--   - reading: the window starts at max{j − d_i + 1, 1} → the window starts at max{j − d + 1, 1}; reason: there is a single usage duration d (p.2); (D) on the same page writes j − d + 1
--   - encoding: the algorithm is Γ-competitive (p.2) → Γ · OPT ≤ P with OPT the optimal offline reward; reason: definition of Γ-competitive on p.2, in the weighted form of p.3
--   - encoding: arrivals 1, …, |U|; periods of length d with a dummy period before the first arrival (p.8) → arrivals Fin n numbered from 0; arrival t lies in period t / d + 1; period 0 is the dummy period; seeds indexed by V × Fin (n + 1); reason: Lean convention; same instances and same runs
--   - encoding: d ∈ ℕ (p.2) → 1 ≤ d, as a field of the instance; reason: the model ("unavailable for the next d − 1 periods") has no meaning at d = 0
-- source:
--   Delong, Farhadi, Niazadeh, Sivan & Udwani, Online Bipartite Matching with Reusable Resources, arXiv:2110.07084v2, Lemma 1, p.6 (proof in Appendix C, p.33); LP (P)/(D), p.6

import Mathlib
import Definitions.Def_ReusableMatching_OPT
import Definitions.Def_ReusableMatching_window

namespace ReusableMatching

/-- **Lemma 1 (dual fitting)** of Delong, Farhadi, Niazadeh, Sivan & Udwani, *Online Bipartite
Matching with Reusable Resources*, arXiv:2110.07084v2, p.6 (proof in Appendix C, p.33):

"Suppose an online algorithm maintains a primal assignment `{x_{i,j}}` with objective value `P`,
and there is a dual assignment `{α_{i,t}, β_j}` with objective value `D` satisfying these
conditions: (i) Reverse weak duality: `P ≥ D`, (ii) Approximate dual feasibility: there exists
`Γ ∈ (0, 1]`, so that `∀ (i, j) ∈ E : β_j + ∑_{t = max{j−d_i+1, 1}}^{j} α_{i,t} ≥ Γ r_i`. Then, the
algorithm is `Γ`-competitive."

Here `D = ∑_{i ∈ V, t ∈ [1, |U|]} α_{i,t} + ∑_{j ∈ U} β_j` is the objective of the dual LP (D)
(p.6), whose variables are non-negative, and `Γ`-competitive means `P ≥ Γ · OPT` with `OPT` the
optimal offline reward.

**Formalization Note.**
* `P` is an arbitrary real number: the conclusion holds for whatever primal value satisfies (i);
  in the application `P` is the expected reward of the algorithm.
* The dual variables are non-negative (the sign constraints `α_{i,t} ≥ 0`, `β_j ≥ 0` of (D)).
* `d_i` is the single usage duration `d` (one duration for all resources, p.2); the window
  `max{j − d + 1, 1} ≤ t ≤ j` is `window I j`. -/
theorem lemma_1 {V : Type*} [Fintype V] {n : ℕ} (I : OBMRRInstance V n) (P : ℝ)
    (α : V → Fin n → ℝ) (βd : Fin n → ℝ) (Γ : ℝ) (hΓ0 : 0 < Γ) (hΓ1 : Γ ≤ 1)
    (hα : ∀ i t, 0 ≤ α i t) (hβ : ∀ j, 0 ≤ βd j)
    (h_rev : (∑ i, ∑ t, α i t) + ∑ j, βd j ≤ P)
    (h_feas : ∀ i j, (i, j) ∈ I.E → Γ * I.r i ≤ βd j + ∑ t ∈ window I j, α i t) :
    Γ * OPT I ≤ P := by sorry

end ReusableMatching
