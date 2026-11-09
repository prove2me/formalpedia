-- Prove2me | Theorems.Thm_StochMatchPoly_lemma_4_3
-- name    : StochMatchPoly.lemma_4_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T07:19:03.618893+00:00
-- url     : https://prove2.me/theorems/58a4b4e3-59e7-4935-9892-d6847f9fba37
-- title:
--   Lemma 4.3 — rounding with a quadratic loss: $\mu(K)\ge|y|-\sum_e y_e^2$
-- statement:
--   For every fractional matching $y$ in a finite simple graph $K$ (a nonnegative edge vector with $y_v=\sum_{e\ni v}y_e\le1$ at every vertex),
--
--   $$\mu(K)\ge|y|-\sum_e y_e^2 ,$$
--
--   where $|y|=\sum_e y_e$ and $\mu(K)$ is the maximum cardinality of a matching of $K$.
--
--   The lemma is the final rounding step of the main proof: a fractional matching with small squared weights contains an integral matching of almost the same size.
--
--   Differences from the source: none.
-- source:
--   S. Behnezhad, Stochastic Matching with Polynomial Degree, arXiv:2611.03367 (preprint, held version, sha256 409beb43bd8ab862a4a4a595be9c08afd92590790382102cb640d81d9b564017), Lemma 4.3, p.10 (PDF p.11)

import Mathlib
import Definitions.Def_StochMatchPoly_mu
import Definitions.Def_StochMatchPoly_load

open Classical

namespace StochMatchPoly

/-- S. Behnezhad, *Stochastic Matching with Polynomial Degree*, arXiv:2611.03367 (held version,
sha256 409beb43…), Lemma 4.3 (Rounding with a quadratic loss), p.10 (PDF p.11).

"For every fractional matching y in a finite simple graph K, µ(K) ≥ |y| − Σ_e y_e²."

**Formalization Note.** A fractional matching is a nonnegative edge vector with every vertex load
at most `1` (§4.1); `µ(K)` is `mu K.edgeFinset`; the sums are over the edges of `K`. -/
theorem lemma_4_3 {V : Type*} [Fintype V] (K : SimpleGraph V) (y : Sym2 V → ℝ)
    (hy : IsFracMatching K y) :
    total K y - ∑ e ∈ K.edgeFinset, y e ^ 2 ≤ (mu K.edgeFinset : ℝ) := by sorry

end StochMatchPoly
