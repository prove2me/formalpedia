-- Prove2me | Theorems.Thm_SingleSampleCombPI_XOS_Supplement_proposition_2_1
-- name    : SingleSampleCombPI.XOS.Supplement.proposition_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:42:14.724625+00:00
-- url     : https://prove2.me/theorems/d3a924c2-1eab-46f7-b466-469ddc368c21
-- title:
--   Proposition 2.1 — Equivalence between one-sided supporting prices and capped-XOS, including attained infinite clause families
-- statement:
--   Let $v:[0,1]^m\to\mathbb R_{\ge0}$ be normalized and monotone. Then
--   $$v\text{ admits one-sided supporting prices at every }x\quad\Longleftrightarrow\quad v\text{ is capped-XOS}.$$
--   Here support at $x$ means a nonnegative vector $q(x)$ satisfying $\langle q(x),x\rangle=v(x)$ and $\langle q(x),y\rangle\le v(y)$ for every $0\le y\le x$. Capped-XOS permits arbitrary infinite clause families whose supremum is attained pointwise. No continuity or concavity is assumed. This identifies the exact divisible valuation class used by the reduction.
--
--   Differences from the source:
--   - encoding: capped-XOS is an attained supremum of an arbitrary family of capped-additive clauses → a set of clauses bounded above by v with a clause equal to v at every cube point; reason: upper-bound plus attainment is exactly the attained-supremum condition; the zero valuation may use a zero clause, consistent with the source’s empty-maximum convention
--   - encoding: valuations and one-sided supporting-price maps on the source allocation domains → published Buyer, Regime and cube interfaces with real-valued functions evaluated only on the allocation domain; reason: the stored demand field is unused in noncomputational continuous statements; no support, continuity or concavity condition is added to the source valuation class
-- source:
--   Shuchi Chawla, Trung Dang, STOC 2027 submission #30 (October 2026), Proposition 2.1, printed p. 8 / PDF p. 10; proof printed 37 / PDF 39.

import Mathlib
import Definitions.Def_SingleSampleCombPI_XOS_Supplement_Continuous

namespace SingleSampleCombPI.XOS.Supplement

/-- Proposition 2.1, printed p. 8 / PDF p. 10. Both directions, the whole
cube, arbitrary attained families, and the source's one-sided support. -/
theorem proposition_2_1 {m : ℕ} (v : Vec m → ℝ)
    (hv : IsValuation .divisible v) :
    (∃ q : Vec m → Vec m, IsSupporting .divisible v q) ↔ IsCappedXOS v := by sorry

end SingleSampleCombPI.XOS.Supplement
