-- Prove2me | Theorems.Thm_ProcessingNetworks_PathCompact_lemma_A_10
-- name    : ProcessingNetworks.PathCompact.lemma_A_10
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:30:07.573989+00:00
-- url     : https://prove2.me/theorems/b5e03ef1-ed0b-4d26-ad49-f45908c92a89
-- title:
--   Lemma A.10 — monotone paths converging at the rationals to a continuous limit converge u.o.c.
-- statement:
--   Let $\{f_n\}\subset D$ be a sequence of nondecreasing real-valued paths on $\mathbb R_+$ and let $f\in C$ be a continuous function on $\mathbb R_+$. If $f_n(t)\to f(t)$ for every rational $t\ge0$, then
--
--   $$f_n\to f\quad\text{u.o.c.},$$
--
--   that is, $\sup_{0\le s\le t}|f_n(s)-f(s)|\to0$ for every $t>0$.
--
--   The lemma (from Dai 1995) upgrades convergence on a countable dense set to uniform convergence on compacts for monotone paths, and is the last step of Lemma A.11.
--
--   Differences from the source:
--   - encoding: time set ℝ₊, index set ℕ = {1, 2, …}, a subsequence {n_k} → ℝ≥0, ℕ (from 0), a strictly increasing φ : ℕ → ℕ; reason: Lean convention; same instances
--   - encoding: D (right continuous on ℝ₊ with left limits on (0, ∞)) and C (continuous functions) → the public predicate RBMSensitivity.IsRCLL and Continuous; reason: IsRCLL asks right continuity at every t and a left limit at every t, the latter being automatic at t = 0 where the left filter is trivial; same paths
--   - encoding: for all rational t ≥ 0 → for every t : ℝ≥0 equal to the cast of some q : ℚ; reason: same set of times
-- source:
--   Dai & Harrison, Processing Networks (pre-publication draft 2020-4-2, spnbook.org), Appendix A, §A.3, Lemma A.10, p.260 (PDF 276)

import Mathlib
import Definitions.Def_RBMSensitivity_IsRCLL
import Definitions.Def_ProcessingNetworks_PathCompact_ConvergesUOC

open Filter Topology
open scoped NNReal

namespace ProcessingNetworks.PathCompact

/-- **Lemma A.10** (monotone paths converging at the rationals to a continuous limit converge
u.o.c.), Dai & Harrison, *Processing Networks* (pre-publication draft 2020-4-2, spnbook.org),
Appendix A, §A.3, Lemma A.10, p.260 (PDF 276).

Let `{fₙ} ⊂ D` be a sequence of nondecreasing functions on `ℝ₊` and `f ∈ C` a continuous
function on `ℝ₊`. If `fₙ(t) → f(t)` for all rational `t ≥ 0`, then `fₙ → f` u.o.c.

**Formalization Note.** Time is `ℝ≥0`; "rational `t ≥ 0`" is a `t : ℝ≥0` equal to the cast of
some `q : ℚ`. `D` (real-valued càdlàg paths) is `RBMSensitivity.IsRCLL`, `C` is
`Continuous`, "nondecreasing" is `Monotone`, u.o.c. is `ConvergesUOC` (Definition A.6). -/
theorem lemma_A_10 (fs : ℕ → ℝ≥0 → ℝ) (hD : ∀ n, RBMSensitivity.IsRCLL (fs n))
    (hmono : ∀ n, Monotone (fs n)) (f : ℝ≥0 → ℝ) (hf : Continuous f)
    (hrat : ∀ t : ℝ≥0, (∃ q : ℚ, (q : ℝ) = (t : ℝ)) →
      Tendsto (fun n => fs n t) atTop (𝓝 (f t))) :
    ConvergesUOC fs f := by sorry

end ProcessingNetworks.PathCompact
