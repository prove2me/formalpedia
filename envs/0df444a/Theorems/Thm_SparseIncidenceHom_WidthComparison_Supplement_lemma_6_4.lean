-- Prove2me | Theorems.Thm_SparseIncidenceHom_WidthComparison_Supplement_lemma_6_4
-- name    : SparseIncidenceHom.WidthComparison.Supplement.lemma_6_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:18:12.495202+00:00
-- url     : https://prove2.me/theorems/74ec35f8-6c55-4576-a602-175586ef8c46
-- title:
--   Lemma 6.4 — cheap hubs in pseudometrics
-- statement:
--   There is an absolute constant $C_H>0$ such that, for every pseudometric $d$ on $[k]$ with $k\ge2$, some $z\in[k]$ satisfies
--   $$\sum_{u\in[k]}d(z,u)\le C_H\log k\max_{\substack{\varnothing\ne A,B\subseteq[k]\\A\cap B=\varnothing}}\min\{|A|,|B|\}\,d(A,B).\tag{10}$$
--
--   Here a pseudometric is nonnegative, symmetric, vanishes on the diagonal and satisfies the triangle inequality; distinct points may be at distance zero, and $d(A,B)=\min_{i\in A,j\in B}d(i,j)$. The lemma supplies a hub whose total distance to all points is small whenever no two large groups are far apart.
--
--   **Formalization Note** $\log$ is to base two; $[k]$ is `Fin k`; the maximum is a supremum over a finite nonempty set.
--
--   Differences from the source: none.
-- source:
--   Matthias Lanzinger, STOC 2027 submission #662 (October 2026), p. 24, Lemma 6.4 (inequality (10)); proof pp. 24–25

import Mathlib
import Definitions.Def_SparseIncidenceHom_WidthComparison_Supplement_Widths

namespace SparseIncidenceHom.WidthComparison.Supplement

open SparseIncidenceHom.WidthComparison

/-- Lanzinger, STOC 2027 submission #662, Lemma 6.4, p. 24 (inequality (10)). -/
theorem lemma_6_4 : ∃ C_H : ℝ, 0 < C_H ∧ HubBound C_H := by sorry

end SparseIncidenceHom.WidthComparison.Supplement
