-- Prove2me | Theorems.Thm_RiskExpPG_lemma_16
-- name    : RiskExpPG.lemma_16
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T20:26:20.403413+00:00
-- url     : https://prove2.me/theorems/ffd3a892-e93a-4c14-9c93-b87aeb33c8c1
-- title:
--   Lemma 16 — $-\mathrm dg^{(M)}/\mathrm d\Lambda$ is uniformly positive
-- statement:
--   For any $I=[a,b]\subset\mathbb R$, the value of $-\mathrm dg^{(M)}(\theta,\Lambda)/\mathrm d\Lambda$ is uniformly bounded away from $0$ over $\theta\in\mathbb R^l$, $\Lambda\in I$ and $M>1$.
--
--   Together with Lemma 15, this shows that the expected statistic $f^{(M)}$ is a uniformly positive multiple of the gradient of the truncated cost.
--
--   Differences from the source:
--   - reading: no assumptions named in the statement → Assumptions 1 and 2; reason: these are the hypotheses of Lemmas 12 and 13 (pp.37, 39), on which the proof rests; Assumption 3 is not used
--   - reading: bounded functions and bounded derivatives in Assumptions 2 and 3 → bounds uniform in θ, with no continuity of the second derivative; reason: Lemma 12's proof and Lemma 17 need uniform bounds; the page says twice differentiable, not C²
--   - encoding: expectations over the first return time τ_{x*} → sums over finite excursions, in ℝ≥0∞ or as a real sum with its summability asserted; reason: Assumption 1 makes τ_{x*} finite almost surely, so the values agree and +∞ stays representable
--   - encoding: −dg^(M)/dΛ → −deriv of the real-valued g^(M)(θ, ·); reason: deriv is 0 where the derivative does not exist, so a positive lower bound also rules that out
-- source:
--   Moharrami, Murthy, Roy & Srikant, A Policy Gradient Algorithm for the Risk-Sensitive Exponential Cost MDP, arXiv:2202.04157v2, Lemma 16, p.41

import Mathlib
import Definitions.Def_RiskExpPG_Chain
import Definitions.Def_RiskExpPG_Model
open Filter Topology MeasureTheory
open scoped ENNReal

namespace RiskExpPG

/-- **Lemma 16** (arXiv:2202.04157v2, p.41). For any `I = [a, b]`, the value of `-dg^(M)(θ, Λ)/dΛ` is
uniformly bounded away from `0` over `θ ∈ ℝ^l`, `Λ ∈ I` and `M > 1`. -/
theorem lemma_16 {X : Type*} [Fintype X] [DecidableEq X] {l : ℕ} (m : Model X l)
    (hm : m.IsValid) (h1 : m.Assumption1) (h2 : m.Assumption2)
    (a b : ℝ) :
    ∃ c > 0, ∀ θ, ∀ Λ ∈ Set.Icc a b, ∀ M, 1 < M →
      c ≤ -deriv (fun Λ' => m.gTruncReal M (θ, Λ')) Λ := by sorry

end RiskExpPG
