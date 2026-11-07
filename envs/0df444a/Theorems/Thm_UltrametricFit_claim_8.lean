-- Prove2me | Theorems.Thm_UltrametricFit_claim_8
-- name    : UltrametricFit.claim_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:46:02.262254+00:00
-- url     : https://prove2.me/theorems/ee4c0434-6ef3-44cc-8ade-44482299fef6
-- title:
--   Claim 8, p.9 — nodes of a merge forest have small self-distance
-- statement:
--   Let $d$ be a pseudometric and $\delta\ge0$. Each node $A$ of a $\delta$-merge forest satisfies
--   $$d(A,A)\le\delta,$$
--   where $d(A,A)$ averages over all ordered pairs, including $i=j$. Thus the merge condition, which only concerns the two children at each step, controls the whole node.
--
--   Differences from the source:
--   - generalization: a metric $d$ → a pseudometric (zero distances between distinct species are allowed); reason: every metric is a pseudometric, and the paper applies the result to the LP layers $x_\ell$, which it calls technically a pseudometric (p.2)
--   - encoding: $\delta$-merge forest for a $\delta$ left unspecified in §4.1 → $0\le\delta$; reason: the paper's $\delta$ lies in $(0,0.5)$ (§3); the bound fails for a singleton when $\delta<0$, so this excludes no instance of the paper
-- source:
--   Charikar, Gao, Fitting Ultrametrics under any ℓ_p Objective, STOC 2027 submission (manuscript sha256 87af12a2…), Claim 8, p.9

import Mathlib
import Definitions.Def_UltrametricFit_IsMergeNode

namespace UltrametricFit

/-- **Claim 8**, Charikar, Gao, STOC 2027 submission (manuscript sha256 87af12a2…), p.9: each node
of a δ-merge forest has `d(A, A) ≤ δ`.

**Formalization Note.** `0 ≤ δ` is needed for a singleton, where `d(A, A) = 0`; the paper's `δ` lies
in `(0, 0.5)` (§3, p.8). -/
theorem claim_8 {n : ℕ} (d : Fin n → Fin n → ℝ) (hd : IsPseudometric d) (δ : ℝ) (hδ : 0 ≤ δ)
    (A : Finset (Fin n)) (hA : IsMergeNode d δ A) :
    avgDist d A A ≤ δ := by sorry

end UltrametricFit
