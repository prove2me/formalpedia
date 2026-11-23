-- Prove2me | Theorems.Thm_ReentrantScheduling_FBFS_Supplement_theorem5_multiple_stability
-- name    : ReentrantScheduling.FBFS.Supplement.theorem5_multiple_stability
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T13:17:24.835614+00:00
-- url     : https://prove2.me/theorems/d3ed1f5e-4da0-4671-a635-4eb6d6748333
-- title:
--   Theorem 5 (corrected: positive service times) — IFBFS, ULBFS and CFLBFS delay stability
-- statement:
--   Consider finitely many part types sharing finitely many service centers, with $m_\sigma\ge1$ machines at center $\sigma$. Each type follows a finite nonempty route. Suppose $\lambda_p,\gamma_p\ge0$, type-$p$ arrivals satisfy
--
--   $$u_p(t)-u_p(s)\le\lambda_p(t-s)+\gamma_p\quad(0\le s\le t),$$
--
--   and the combined load at each center satisfies
--
--   $$\sum_p\lambda_p\sum_{i:\,\sigma_{p,i}=\sigma}\frac{\tau_{p,i}}{m_\sigma}<1.$$
--
--   For every global buffer ranking in any of the three families IFBFS, ULBFS and CFLBFS, every admissible nonidling nonpreemptive run is stable:
--
--   $$\exists\Gamma\ge0\quad\forall p\ \forall a\text{ of type }p,\qquad e(a)\le\alpha(a)+\Gamma.$$
--
--   IFBFS preserves each type's forward route globally. ULBFS concatenates whole reverse routes in any type order. CFLBFS permits any partition into forward types and contiguous reverse-route blocks, including empty sides. All three clauses appear in the Lean statement. Capacity counts all types sharing a center, and the bound includes initial parts and may depend on the run and its initial contents. This companion theorem extends the stability conclusion to interacting routes.
--
--   **Formalization Note** Each route uses the published raw Line and Run definitions. Types and buffers are 0-based, and never-served parts have infinite exit. Every rank and every CFLBFS partition is quantified over. The positive-time pin and within-type head-order convention are disclosed below.
--
--   Differences from the source:
--   - correction: Processing times in the printed setting have no explicit strict positivity hypothesis → Every processing time is strictly positive in the required immutable base Line; reason: The brief mandates the published Line and its disclosed positive-time pin; the source busy-period proof divides by a processing time (p. 1409). Zero processing times are excluded, not proved covered here
--   - encoding: Types, stages and global buffer positions are 1-based finite labels → Types and stages are Fin indices and the global ranking is a bijection onto consecutive 0-based ranks; reason: All finite routes and all global rankings remain represented
--   - reading: Head-of-buffer dispatch and the line order are implicit within each type → Each type inherits the published initial-first, deeper-initial-first and release-order FIFO convention; reason: This is the immutable base convention; it resolves simultaneous arrivals without imposing any order between different types
--   - encoding: Stability is (4) for every part of a multitype system → One nonnegative real Γ bounds exits of every type in WithTop ℝ; reason: Finitely many types allow a common maximum of their delay bounds; infinity is preserved until ruled out by the conclusion
-- source:
--   Lu & Kumar, Distributed Scheduling Based on Due Dates and Buffer Priorities, IEEE TAC 36(12), 1991, p. 1414, Theorem 5, (18), (19), IFBFS, ULBFS and CFLBFS; p. 1413, §VII

import Mathlib
import Definitions.Def_ReentrantScheduling_FBFS_Supplement_Policies

namespace ReentrantScheduling.FBFS.Supplement

/-- Theorem 5, p. 1414: all global IFBFS, ULBFS, and CFLBFS rankings are stable. -/
theorem theorem5_multiple_stability (N : MultipleLines) (lam γ : Fin N.P → ℝ)
    (hlam : ∀ p, 0 ≤ lam p) (hγ : ∀ p, 0 ≤ γ p) (hload : N.BelowCapacity lam)
    (R : MultipleRun N) (harr : R.Arrivals lam γ) (β : N.Ranking) :
    (N.IFBFS β → R.Admissible (fun a => (β a).val) → R.Stable) ∧
    (N.ULBFS β → R.Admissible (fun a => (β a).val) → R.Stable) ∧
    (∀ P_L : Set (Fin N.P), N.CFLBFS β P_L →
      R.Admissible (fun a => (β a).val) → R.Stable) := by sorry

end ReentrantScheduling.FBFS.Supplement
