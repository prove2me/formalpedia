-- Prove2me | Theorems.Thm_ParetoNCSched_smith_rule
-- name    : ParetoNCSched.smith_rule
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T03:09:40.276769+00:00
-- url     : https://prove2.me/theorems/6e0c0800-fa73-46e8-a8fc-a6f46aba5626
-- title:
--   Smith's rule — $\mathrm{OPT}(p)=\Phi(p)$
-- statement:
--   For every $p\in(0,\infty)^n$, the optimal total completion time over all preemptive single-machine schedules equals
--   $$\mathrm{OPT}(p)=\Phi(p)=\sum_j p_j+\sum_{i<j}\min(p_i,p_j).$$
--
--   The paper cites this classical fact (Smith 1956; Motwani–Phillips–Torng 1994) and uses it to turn the invariant $F\le R\,\Phi(e)$ into the bound $\mathrm{MRC}_R\le R\,\mathrm{OPT}$ and in the consistency analysis.
--
--   Differences from the source:
--   - encoding: jobs 1, …, n and positions σ(1), …, σ(n) → jobs `Fin n`, 0-based positions, σ k the job at position k; reason: relabelling only; same instances
--   - encoding: OPT(p), the optimal total completion time → the infimum of Σⱼ Cⱼ over all measurable rate schedules (`IsSchedule`), in [0, ∞]; reason: this is the meaning of "optimal total completion time" for the schedules of Appendix A; the paper evaluates it by Smith's rule, a separate milestone; conditions imposed at every real t, with Borel measurable rates: a schedule on [0, ∞) extends by 0 and changes on a null set only, so the set of costs is the paper's
--   - encoding: an instance of n jobs (the suprema of p.15 range over n ≥ 1) → every n : ℕ, n = 0 included; reason: with no jobs every clause is trivial or vacuous, so the case adds nothing and removes nothing
-- source:
--   Benomar–Perchet, Pareto-optimal Non-Clairvoyant Scheduling with Predictions, manuscript (STOC 2027 submission, sha256 852cb174…), Appendix A, Notation, p.15 (Smith's rule [Smi56], see also [MPT94])

import Mathlib
import Definitions.Def_ParetoNCSched_OPT
import Definitions.Def_ParetoNCSched_Phi
open scoped ENNReal
open MeasureTheory Set

namespace ParetoNCSched

/-- **Smith's rule: `OPT(p) = Φ(p)`.** Benomar–Perchet, *Pareto-optimal Non-Clairvoyant Scheduling with Predictions*, manuscript (STOC 2027 submission, sha256 852cb174…), Appendix A, Notation, p.15: "For e ∈ ℝⁿ≥0 let
Φ(e) = Σⱼ eⱼ + Σ_{i<j} min(eᵢ, eⱼ). Smith's rule [Smi56] gives OPT(p) = Φ(p) (see also [MPT94])."

**Formalization Note.** `OPT` is the infimum of the total completion time over all measurable rate
schedules (`IsSchedule`), in `ℝ≥0∞`; the statement says it equals `Φ(p)` (both directions: some
schedule attains `Φ(p)`, and none does better). -/
theorem smith_rule {n : ℕ} (p : Fin n → ℝ) (hp : ∀ j, 0 < p j) :
    OPT p = ENNReal.ofReal (Phi p) := by sorry

end ParetoNCSched
