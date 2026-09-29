-- Prove2me | Theorems.Thm_ProbabilityTheory_cond_isProbabilityMeasure_of_real
-- name    : ProbabilityTheory.cond_isProbabilityMeasure_of_real
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-21T17:47:11.794926+00:00
-- url     : https://prove2.me/theorems/118e77be-7336-40ff-a8b4-e87a0787663b
-- title:
--   Conditioning on a set of non-zero measure yields a probability measure
-- statement:
--   **Conditioning a measure on a set of non-zero real measure gives a probability measure.**
--
--   For a measure $\mu$ on $\alpha$ and a set $s$ with $\mu_{\mathbb{R}}(s) \ne 0$, the conditional
--   measure
--
--   $$\mu[\,\cdot\mid s\,] \;=\; \frac{1}{\mu(s)}\,\mu\!\restriction_s$$
--
--   is a probability measure, i.e. it assigns total mass $1$.
--
--   The hypothesis is stated with the **real-valued** measure $\mu_{\mathbb{R}}(s) \ne 0$ rather
--   than $\mu(s) \ne 0$, and this is the useful form: `Measure.real` sends $\infty$ to $0$, so
--   $\mu_{\mathbb{R}}(s) \ne 0$ simultaneously rules out $\mu(s) = 0$ **and** $\mu(s) = \infty$.
--   Both exclusions are necessary — conditioning on a null set is undefined, and conditioning on a
--   set of infinite measure does not normalise — so the single real-valued hypothesis captures
--   exactly the right condition where the `ENNReal` version would need two.
--
--   This is the standing hypothesis-discharging lemma in probabilistic arguments: once
--   $\mu[\,\cdot\mid s\,]$ is known to be a probability measure, the whole `IsProbabilityMeasure`
--   API (total mass, expectations, entropy) becomes available for it.
--
--   **Formalization note.** `μ[|s]` is Mathlib's notation for `ProbabilityTheory.cond μ s`, and
--   `μ.real s` is `(μ s).toReal`.
-- source:
--   Adapted from the Polynomial Freiman–Ruzsa (PFR) project (original authors Terence Tao and the PFR project contributors, Apache-2.0), as vendored in `Salt/Entropy/` of the Salt project, https://github.com/jyh/salt (Apache-2.0, Jason Hickey).

import Mathlib

namespace ProbabilityTheory

open MeasureTheory ProbabilityTheory in
theorem cond_isProbabilityMeasure_of_real {α : Type*} {_ : MeasurableSpace α} {μ : Measure α}
    {s : Set α} (hcs : μ.real s ≠ 0) :
    IsProbabilityMeasure μ[|s] := by sorry

end ProbabilityTheory
