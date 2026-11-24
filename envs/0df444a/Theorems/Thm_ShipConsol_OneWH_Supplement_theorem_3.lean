-- Prove2me | Theorems.Thm_ShipConsol_OneWH_Supplement_theorem_3
-- name    : ShipConsol.OneWH.Supplement.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T06:29:50.817828+00:00
-- url     : https://prove2.me/theorems/ab81b8d7-1bd7-4c2d-bde7-1bb6d8a444bd
-- title:
--   Theorem 3 — six symmetric boundary regions and feasible optimal policy coverage
-- statement:
--   Consider the symmetric two-warehouse fixed-cost model with common nonnegative convex non-increasing cost F, d≥1, and independent arrival probabilities (α,β,α)∈[0,1]^3. For every t≥1 there are six integer boundaries, each a function of the other two minimum slacks, that license a feasible Bellman-optimal complete shipping policy at every state. They obey
--
--   $$\tau_A^{AB}(z_B,z_C)\le\tau_A^A(z_B,z_C),\qquad \tau_C^{BC}(z_A,z_B)\le\tau_C^C(z_A,z_B).$$
--
--   The six shipment implications are: crossing τ_A^{AB} in z_A or τ_B^1 in z_B permits an optimal completion shipping A and B from W1; crossing τ_A^A in z_A permits shipment of A from W1. Crossing τ_C^{BC} in z_C or τ_B^2 in z_B permits an optimal completion shipping B and C from W2; crossing τ_C^C in z_C permits shipment of C from W2. Moreover,
--
--   $$\tau_A^{AB}(\infty,z_C)=\tau_A^A(\infty,z_C),\qquad \tau_C^{BC}(z_A,\infty)=\tau_C^C(z_A,\infty).$$
--
--   All active slacks range over {1,…,d}; the other coordinates may be absent. Coverage requires an optimal complete action with every shipment licensed by the six regions, so a witness cannot simply turn all regions off. Individual recommendations mean existence of an optimal completion, allowing ties and independent action at the other warehouse.
--
--   Differences from the source:
--   - reading: boundaries completely characterize an optimal policy → six sufficient optimal-completion regions plus a globally defined optimal complete-action selector whose shipments are all licensed by the regions; reason: p. 17 and footnote 20 allow indifference between distinct B assignments; exact equivalence with every optimal action would fail on ties, and all-zero regions are excluded by coverage
--   - encoding: ∞ for no orders; fixed-cost minimum over warehouse assignments → WithTop natural slacks and a finite set of exclusive B assignments; reason: the explicit assignment minimum is the displayed f of p. 15; absence costs zero and no B order can be assigned twice
--   - encoding: F1=F2 and α_A=α_C → one common F and arrival parameters (α,β,α); reason: this parameterizes every symmetric source instance without assuming β=α
-- source:
--   Wei, Kapuscinski & Jasin, Shipping Consolidation across Two Warehouses with Delivery Deadline and Expedited Options for E-commerce and Omni-channel Retailers, author's manuscript, SSRN 2920899 (M&SOM 2020, doi:10.1287/msom.2020.0903), pinned PDF sha256 2cc7647135cddd3db3d07ad21c65ac52502947d2dde5f337f3ab9948547f0a03, Theorem 3, p. 16; proof OA5–OA8 (PDF37–40)

import Mathlib
import Definitions.Def_ShipConsol_OneWH_Supplement_TwoWarehouse

namespace ShipConsol.OneWH.Supplement

theorem theorem_3 (D : SymmetricData) (hD : D.SourceData) (t : ℕ) (ht : 1 ≤ t) :
    ∃ b : Boundaries, sixRegions D t b := by sorry

end ShipConsol.OneWH.Supplement
