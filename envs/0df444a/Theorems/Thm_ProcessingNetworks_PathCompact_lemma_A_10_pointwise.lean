-- Prove2me | Theorems.Thm_ProcessingNetworks_PathCompact_lemma_A_10_pointwise
-- name    : ProcessingNetworks.PathCompact.lemma_A_10_pointwise
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:30:00.127331+00:00
-- url     : https://prove2.me/theorems/d140332b-8a7e-4080-95c5-2023cbda3db1
-- title:
--   Proof of Lemma A.10 — monotone paths converging at the rationals to a continuous limit converge at every time
-- statement:
--   Let $\{f_n\}\subset D$ be real-valued paths on $\mathbb R_+$ that are nondecreasing, let $f\in C$ be continuous, and assume $f_n(t)\to f(t)$ for every rational $t\ge0$. Then
--
--   $$f_n(t)\to f(t)\qquad\text{for every }t\in\mathbb R_+.$$
--
--   This is the first step in the proof of Lemma A.10: monotonicity squeezes $f_n(t)$ between its values at nearby rational times, and continuity of $f$ closes the gap.
--
--   Differences from the source:
--   - encoding: time set ℝ₊, index set ℕ = {1, 2, …}, a subsequence {n_k} → ℝ≥0, ℕ (from 0), a strictly increasing φ : ℕ → ℕ; reason: Lean convention; same instances
--   - encoding: D (right continuous on ℝ₊ with left limits on (0, ∞)) and C (continuous functions) → the public predicate RBMSensitivity.IsRCLL and Continuous; reason: IsRCLL asks right continuity at every t and a left limit at every t, the latter being automatic at t = 0 where the left filter is trivial; same paths
--   - encoding: for all rational t ≥ 0 → for every t : ℝ≥0 equal to the cast of some q : ℚ; reason: same set of times
-- source:
--   Dai & Harrison, Processing Networks (pre-publication draft 2020-4-2, spnbook.org), Appendix A, §A.3, proof of Lemma A.10, p.260 (PDF 276), unnumbered claim

import Mathlib
import Definitions.Def_RBMSensitivity_IsRCLL
import Definitions.Def_ProcessingNetworks_PathCompact_ConvergesUOC

open Filter Topology
open scoped NNReal

namespace ProcessingNetworks.PathCompact

/-- **Pointwise step of Lemma A.10** (convergence at the rationals gives convergence everywhere),
Dai & Harrison, *Processing Networks* (pre-publication draft 2020-4-2, spnbook.org), Appendix A,
§A.3, proof of Lemma A.10, p.260 (PDF 276), unnumbered claim: "because `fₙ` is nondecreasing and
`f` is continuous, one can check that `fₙ(t) → f(t)` for every `t ∈ ℝ₊`".

Under the hypotheses of Lemma A.10 — `{fₙ} ⊂ D` nondecreasing on `ℝ₊`, `f ∈ C`, and
`fₙ(t) → f(t)` for every rational `t ≥ 0` — one has `fₙ(t) → f(t)` for every `t ≥ 0`.

**Formalization Note.** Time is `ℝ≥0`; "rational `t ≥ 0`" is a `t : ℝ≥0` equal to the cast of
some `q : ℚ`. `D` is `RBMSensitivity.IsRCLL` (right continuous with left limits), `C` is
`Continuous`. -/
theorem lemma_A_10_pointwise (fs : ℕ → ℝ≥0 → ℝ) (hD : ∀ n, RBMSensitivity.IsRCLL (fs n))
    (hmono : ∀ n, Monotone (fs n)) (f : ℝ≥0 → ℝ) (hf : Continuous f)
    (hrat : ∀ t : ℝ≥0, (∃ q : ℚ, (q : ℝ) = (t : ℝ)) →
      Tendsto (fun n => fs n t) atTop (𝓝 (f t))) :
    ∀ t : ℝ≥0, Tendsto (fun n => fs n t) atTop (𝓝 (f t)) := by sorry

end ProcessingNetworks.PathCompact
