-- Prove2me | Theorems.Thm_TreeEdgeRankPC_lemma_4_9
-- name    : TreeEdgeRankPC.lemma_4_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T06:36:46.657247+00:00
-- url     : https://prove2.me/theorems/294bd7fb-3fb4-4b2f-8d0b-cf0db36f29cf
-- title:
--   Lemma 4.9 — the selector leaves the $u$-messages on $H_e$ and the $v$-messages on $L_e$
-- statement:
--   Let $e\ge16$ and $0\le u_j,v_k<2^{e-14}$. At clock $e$, suppose the residuals consist of the selector requirements (4.3), a signal $H_e$ or $L_e$, and other residuals below $2^{e-14}$. Processing the clocks $e,e-1,\dots,e-14$ causes no rejection and leaves all other residuals unchanged. Among the signal and selector requirements, the remaining residuals are exactly the positive entries of:
--
--   1. $u_1,\dots,u_6$ on $H_e$;
--   2. $v_1,\dots,v_4$ on $L_e$.
--
--   The selector is the gadget that lets a signal choose which residuals survive, and so plays the role of a wire.
--
--   Differences from the source:
--   - encoding: "causes no rejection", "leaves all other residuals unchanged", "the remaining residuals are exactly" → one equation of multisets for `runClocks`, with value `some`; reason: the single equation says all three
--   - encoding: the signal requirements and the families u, v → the list `sigH e`/`sigL e` as a multiset; 0-based `Fin 6`, `Fin 4`; reason: the same multiset of requirements
--   - encoding: other residuals → a multiset of positive numbers below 2^{e−14}; reason: a zero residual has been removed, p.16
-- source:
--   Giliberti–Hajiaghayi–Yun, Parallel Edge Ranking of Trees, arXiv:2610.12438 (held version of 2026-11-02, sha256 9e04ca7b…), Lemma 4.9, p.18; eq. (4.3), p.18

import Mathlib
import Definitions.Def_TreeEdgeRankPC_GreedyAllocation
import Definitions.Def_TreeEdgeRankPC_Gadgets

namespace TreeEdgeRankPC

/-- **Lemma 4.9 (Selector)**, §4.2, p.18, arXiv:2610.12438 (held version of 2026-11-02, sha256 9e04ca7b…): "At clock e ≥ 16, suppose the residuals consist of the
requirements in Equation (4.3), a signal H_e or L_e, and other residuals below 2^{e−14}. Processing clocks e,
e−1, ..., e−14 causes no rejection and leaves all other residuals unchanged. Among the signal and selector
requirements, the remaining residuals are exactly the positive entries of: u1, ..., u6 on H_e; v1, ..., v4 on L_e."

**Formalization Note.** The messages satisfy `0 ≤ u_j, v_k < 2^{e−14}` as fixed before (4.3). `R` is the
multiset of other residuals; residuals are positive by definition (p.16: a zero residual has been removed). The
multiset equation says all at once: no rejection, `R` unchanged, and exactly the positive entries remain. -/
theorem lemma_4_9 (e : ℕ) (he : 16 ≤ e) (u : Fin 6 → ℕ) (v : Fin 4 → ℕ)
    (hu : ∀ j, u j < 2 ^ (e - 14)) (hv : ∀ k, v k < 2 ^ (e - 14))
    (R : Multiset ℕ) (hR : ∀ r ∈ R, 0 < r ∧ r < 2 ^ (e - 14)) :
    runClocks e (e - 14) ((selector e u v : Multiset ℕ) + (sigH e : Multiset ℕ) + R) =
        some (R + positives u) ∧
    runClocks e (e - 14) ((selector e u v : Multiset ℕ) + (sigL e : Multiset ℕ) + R) =
        some (R + positives v) := by sorry

end TreeEdgeRankPC
