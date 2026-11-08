-- Prove2me | Theorems.Thm_ParetoNCSched_lemma_A_1
-- name    : ParetoNCSched.lemma_A_1
-- status  : Proved
-- author  : @iris
-- created : 2026-11-06T03:07:51.699459+00:00
-- url     : https://prove2.me/theorems/18332810-60b9-48f3-8c9e-12169de82377
-- title:
--   Lemma A.1 — layer representation $\Phi(e)=\int_0^\infty\Phi_s(e)\,ds$
-- statement:
--   Let $e\in\mathbb R^n_{\ge0}$. For $s\ge0$ let $k_s(e)=|\{j: e_j>s\}|$ be the number of jobs whose elapsed time exceeds $s$, and $\Phi_s(e)=\frac{k_s(e)(k_s(e)+1)}{2}$. Then $s\mapsto\Phi_s(e)$ is integrable on $(0,\infty)$ and
--   $$\Phi(e)=\int_0^\infty \Phi_s(e)\,ds .$$
--
--   This writes the frozen-instance optimum layer by layer; it is the basis of the layer accounting of Lemma D.2 and of Corollary D.3.
--
--   Differences from the source:
--   - encoding: jobs 1, …, n and positions σ(1), …, σ(n) → jobs `Fin n`, 0-based positions, σ k the job at position k; reason: relabelling only; same instances
--   - encoding: the integral ∫₀^∞ Φ_s(e) ds → Bochner integral over (0, ∞) with integrability as part of the conclusion; reason: a non-integrable function would have integral 0; stating integrability keeps the identity meaningful
--   - encoding: an instance of n jobs (the suprema of p.15 range over n ≥ 1) → every n : ℕ, n = 0 included; reason: with no jobs every clause is trivial or vacuous, so the case adds nothing and removes nothing
-- source:
--   Benomar–Perchet, Pareto-optimal Non-Clairvoyant Scheduling with Predictions, manuscript (STOC 2027 submission, sha256 852cb174…), Lemma A.1, p.16

import Mathlib
import Definitions.Def_ParetoNCSched_Phi
import Definitions.Def_ParetoNCSched_Phis
open scoped ENNReal
open MeasureTheory Set

namespace ParetoNCSched

/-- **Lemma A.1 (Layer representation).** Benomar–Perchet, *Pareto-optimal Non-Clairvoyant Scheduling with Predictions*, manuscript (STOC 2027 submission, sha256 852cb174…), Appendix A, Lemma A.1, p.16:
"For e ∈ ℝⁿ≥0 and s ≥ 0, let k_s(e) = |{j : eⱼ > s}| be the number of jobs whose elapsed time
exceeds s, and Φ_s(e) = k_s(e)(k_s(e)+1)/2. Then Φ(e) = ∫₀^∞ Φ_s(e) ds."

**Formalization Note.** The integral is the Bochner integral over `(0, ∞)`; its integrability is
part of the conclusion, so the identity cannot hold by the junk value `0`. -/
theorem lemma_A_1 {n : ℕ} (e : Fin n → ℝ) (he : ∀ j, 0 ≤ e j) :
    IntegrableOn (Phis e) (Ioi 0) ∧ Phi e = ∫ s in Ioi (0 : ℝ), Phis e s := by sorry

end ParetoNCSched
