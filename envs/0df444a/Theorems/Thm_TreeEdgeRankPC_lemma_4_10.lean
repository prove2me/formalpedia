-- Prove2me | Theorems.Thm_TreeEdgeRankPC_lemma_4_10
-- name    : TreeEdgeRankPC.lemma_4_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T06:36:49.084519+00:00
-- url     : https://prove2.me/theorems/abb7b432-aa1a-4b50-9123-116fbe97cecf
-- title:
--   Lemma 4.10 — the AND gate turns two messages into the signal of $x\wedge y$
-- statement:
--   Let $e\ge13$ and $x,y\in\{0,1\}$. At clock $e$, suppose the residuals consist of $\mathcal M^L_e(x)$, $\mathcal M^R_e(y)$, and other residuals below $2^{e-3}+2^{e-4}$. Processing the clocks $e,e-1,e-2$ causes no rejection and leaves all other residuals unchanged. Among the input messages, the remaining residuals at clock $e-3$ are exactly the signal $H_{e-3}$ if $x=y=1$, or the signal $L_{e-3}$ otherwise.
--
--   This is the only gate the simulation needs, since selectors complement the transmitted bit.
--
--   Differences from the source:
--   - encoding: "causes no rejection", "leaves all other residuals unchanged", "the remaining residuals are exactly" → one equation of multisets for `runClocks`, with value `some`; reason: the single equation says all three
--   - encoding: other residuals → a multiset of positive numbers below 2^{e−3} + 2^{e−4}; reason: a zero residual has been removed, p.16
-- source:
--   Giliberti–Hajiaghayi–Yun, Parallel Edge Ranking of Trees, arXiv:2610.12438 (held version of 2026-11-02, sha256 9e04ca7b…), Lemma 4.10, p.19; eq. (4.4), p.18

import Mathlib
import Definitions.Def_TreeEdgeRankPC_GreedyAllocation
import Definitions.Def_TreeEdgeRankPC_Gadgets

namespace TreeEdgeRankPC

/-- **Lemma 4.10 (AND gate)**, §4.2, p.19, arXiv:2610.12438 (held version of 2026-11-02, sha256 9e04ca7b…): "Let e ≥ 13 and x, y ∈ {0, 1}. At clock e, suppose the residuals
consist of 𝓜^L_e(x), 𝓜^R_e(y), and other residuals below 2^{e−3} + 2^{e−4}. Processing clocks e, e − 1, e − 2 causes
no rejection and leaves all other residuals unchanged. Among the input messages, the remaining residuals at
clock e − 3 are exactly the signal H_{e−3} if x = y = 1, or the signal L_{e−3} otherwise."

**Formalization Note.** `R` is the multiset of other residuals, positive by definition. The multiset equation
gives: no rejection, `R` unchanged, and exactly the stated signal remains. -/
theorem lemma_4_10 (e : ℕ) (he : 13 ≤ e) (x y : Bool)
    (R : Multiset ℕ) (hR : ∀ r ∈ R, 0 < r ∧ r < 2 ^ (e - 3) + 2 ^ (e - 4)) :
    runClocks e (e - 2) ((msgL e x : Multiset ℕ) + (msgR e y : Multiset ℕ) + R) =
      some (R + (if x && y then (sigH (e - 3) : Multiset ℕ) else (sigL (e - 3) : Multiset ℕ))) := by sorry

end TreeEdgeRankPC
