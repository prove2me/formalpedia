-- Prove2me | Theorems.Thm_PerishablePricing_Backlog_Supplement_lemma_4
-- name    : PerishablePricing.Backlog.Supplement.lemma_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-23T07:00:51.241812+00:00
-- url     : https://prove2.me/theorems/83fe4610-bd19-4ee0-a6c9-be44dd340fb4
-- title:
--   Lemma 4, p. 288 — shifted positive parts preserve L♮-convexity on both source carriers
-- statement:
--   Let $\mathbb F$ be either $\mathbb R$ or $\mathbb Z$, let $1\le k\le n$, and let $f:\mathbb F^n\to\mathbb R\cup\{+\infty\}$ be L♮-convex. Suppose its infinite extension is nondecreasing in its first $k$ variables on $\mathcal V^+_{n,k}$. If $S$ is its effective domain, then
--
--   $$\hat f(w)=f(H_k(w))$$
--
--   is L♮-convex on its effective domain $\{w\in\mathcal V_{n+1,k}:H_k(w)\in S\}$, where $H_k$ truncates the first $k$ shifted coordinates to their positive parts and shifts all remaining coordinates without truncation. This is the positive-part preservation result used for the lost-sales continuation value.
--
--   **Formalization Note** No total-finite or full-domain hypothesis is imposed, and empty effective domains are allowed. Both carriers specified on p. 287 are included.
--
--   Differences from the source:
--   - encoding: values in $\mathbb R\cup\{+\infty\}$ → finite real values on an arbitrary effective domain $S$ and the full infinite-extension monotonicity condition; reason: the p. 287 domain convention identifies the two encodings, including infinite values outside $S$
--   - encoding: coordinates $1,\ldots,n+1$ over either source carrier → two conjuncts using zero-based `Fin n`, one for reals and one for integers; reason: both source cases and all indices are preserved
-- source:
--   Chen, Pang, Pan, Coordinating Inventory Control and Pricing Strategies for Perishable Products, Oper. Res. 62(2), 2014, https://doi.org/10.1287/opre.2014.1261, Lemma 4, p. 288 (PDF 6)

import Mathlib
import Definitions.Def_PerishablePricing_Backlog_Supplement_PositiveShift

namespace PerishablePricing.Backlog.Supplement

/-- Lemma 4 on both carriers allowed by the source. The effective domain is
arbitrary, including empty domains and +∞ values outside it. -/
theorem lemma_4 :
    (∀ (n k : ℕ), 1 ≤ k → k ≤ n →
      ∀ (S : Set (Fin n → ℝ)) (f : (Fin n → ℝ) → ℝ),
        LNatConvexOn S f → ExtendedMonotoneFirst k S f →
        LNatConvexOn {w ∈ V (n + 1) k | positiveShift k w ∈ S}
          (fun w => f (positiveShift k w))) ∧
    (∀ (n k : ℕ), 1 ≤ k → k ≤ n →
      ∀ (S : Set (Fin n → ℤ)) (f : (Fin n → ℤ) → ℝ),
        LNatConvexOnZ S f → ExtendedMonotoneFirstZ k S f →
        LNatConvexOnZ {w ∈ VZ (n + 1) k | positiveShiftZ k w ∈ S}
          (fun w => f (positiveShiftZ k w))) := by sorry

end PerishablePricing.Backlog.Supplement
