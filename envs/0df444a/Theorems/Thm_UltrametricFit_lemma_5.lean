-- Prove2me | Theorems.Thm_UltrametricFit_lemma_5
-- name    : UltrametricFit.lemma_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:45:06.975664+00:00
-- url     : https://prove2.me/theorems/e91999ff-d16a-478a-8f68-a31811877828
-- title:
--   Lemma 5, p.7 — the triangle inequality for set distances
-- statement:
--   Let $d$ be a pseudometric on $[n]$ and $A,B,C$ non-empty sets of species. Then
--   $$d(A,C)\le d(A,B)+d(B,C).$$
--   The average distance between sets therefore inherits the triangle inequality, which the proof of the approximate inverse Jensen inequality uses for $i\mapsto d(i,B)$.
--
--   Differences from the source:
--   - generalization: a metric $d$ → a pseudometric (zero distances between distinct species are allowed); reason: every metric is a pseudometric, and the paper applies the result to the LP layers $x_\ell$, which it calls technically a pseudometric (p.2)
--   - encoding: sets $A, B, C$ → non-empty finite sets; reason: the page defines $d(A,B)$ only for non-empty sets; this excludes only undefined cases
-- source:
--   Charikar, Gao, Fitting Ultrametrics under any ℓ_p Objective, STOC 2027 submission (manuscript sha256 87af12a2…), Lemma 5, p.7

import Mathlib
import Definitions.Def_UltrametricFit_avgDist

namespace UltrametricFit

/-- **Lemma 5**, Charikar, Gao, *Fitting Ultrametrics under any ℓ_p Objective*, STOC 2027 submission
(manuscript sha256 87af12a2…), p.7: `d(A, C) ≤ d(A, B) + d(B, C)`.

**Formalization Note.** Non-emptiness is the page's domain of `d(·, ·)`; `B = ∅` would make the
statement false through `1/0 = 0`. -/
theorem lemma_5 {n : ℕ} (d : Fin n → Fin n → ℝ) (hd : IsPseudometric d) (A B C : Finset (Fin n))
    (hA : A.Nonempty) (hB : B.Nonempty) (hC : C.Nonempty) :
    avgDist d A C ≤ avgDist d A B + avgDist d B C := by sorry

end UltrametricFit
