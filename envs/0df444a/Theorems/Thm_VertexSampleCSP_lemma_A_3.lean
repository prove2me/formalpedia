-- Prove2me | Theorems.Thm_VertexSampleCSP_lemma_A_3
-- name    : VertexSampleCSP.lemma_A_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T15:54:35.652788+00:00
-- url     : https://prove2.me/theorems/f7fdfe48-4a75-41f2-956f-6fffd431d3a4
-- title:
--   Lemma A.3, p.14 — Rademacher sums of polytopes: $\mathbb E\sup_{u}|\sum_i\epsilon_i h_i(u)|\le2\sqrt2\,\Lambda$
-- statement:
--   Let $I$ be a finite set and, for $i\in I$, let $Z_i=\mathrm{conv}\{c_{ia}:a\in[q]\}\subseteq\mathbb R^D$. Put $\Lambda^2=\sum_{i\in I}\sum_a\|c_{ia}\|^2$ and $h_i=h_{Z_i}$. For independent Rademacher signs $(\epsilon_i)_{i\in I}$,
--
--   $$\mathbb E\sup_{u\in B_2^D}\Big|\sum_{i\in I}\epsilon_i h_i(u)\Big|\le2\sqrt2\,\Lambda.$$
--
--   The bound does not depend on the dimension $D$ or on the alphabet size $q$, which is what allows the sample complexity of the goal theorem to be free of a logarithmic factor.
--
--   **Formalization Note** The real supremum over the ball is of a bounded function, since $|h_i(u)|\le\sum_a\|c_{ia}\|$ there.
--
--   Differences from the source:
--
--   - encoding: finite set I, ℝ^D → finite type J, EuclideanSpace ℝ ι; reason: same objects
--   - encoding: alphabet [q] = {1, …, q} → q ≥ 1 is a hypothesis and the alphabet is Fin q; reason: q = 0 leaves the optimum and the polytopes undefined, so this excludes only undefined cases
--   - encoding: E over Rademacher signs → the finite average radAvg over 2^|J| sign vectors; reason: same expectation
-- source:
--   Chang, Optimal Vertex Sampling for Constraint Satisfaction Problems, STOC 2027 submission (manuscript sha256 1e0edd23…), Lemma A.3, p.14 (PDF p.16)

import Mathlib
import Definitions.Def_VertexSampleCSP_supportFn
import Definitions.Def_VertexSampleCSP_radAvg
open scoped InnerProductSpace

namespace VertexSampleCSP

/-- **Lemma A.3 (Rademacher sums of polytopes).** Chang, *Optimal Vertex Sampling for Constraint
Satisfaction Problems*, STOC 2027 submission (manuscript sha256 1e0edd23…), Lemma A.3, p.14 (PDF
p.16): "Let I be a finite set and, for i ∈ I, let Zi = conv{cia : a ∈ [q]} ⊆ ℝ^D. Put
Λ² = Σ_{i∈I} Σ_a ∥cia∥² and hi = h_{Zi}. Then for independent Rademacher signs (ϵi)_{i∈I},
E sup_{u∈B^D_2} |Σ_{i∈I} ϵi hi(u)| ≤ 2√2 Λ."

**Formalization Note.** The finite set `I` is a finite type `J`; `ℝ^D` is `EuclideanSpace ℝ ι`;
`[q]` is `Fin q` with `q ≥ 1`, so each `Z_i` is a nonempty compact polytope. The expectation over the
signs is the average `radAvg` over the `2^{|J|}` sign vectors. The supremum over the closed unit ball
is a real `sSup`; the function `u ↦ |Σ ϵ_i h_i(u)|` is bounded on the ball (each `|h_i(u)|` is at most
`Σ_a ‖c_{ia}‖`), so this is the true supremum and not a junk value. -/
theorem lemma_A_3 {J ι : Type*} [Fintype J] [DecidableEq J] [Fintype ι] {q : ℕ} (hq : 0 < q)
    (c : J → Fin q → EuclideanSpace ℝ ι) :
    radAvg (fun ϵ : J → ℝ =>
        sSup ((fun u => |∑ i, ϵ i * supportFn (convexHull ℝ (Set.range (c i))) u|) ''
          Metric.closedBall 0 1))
      ≤ 2 * Real.sqrt 2 * Real.sqrt (∑ i, ∑ a, ‖c i a‖ ^ 2) := by sorry

end VertexSampleCSP
