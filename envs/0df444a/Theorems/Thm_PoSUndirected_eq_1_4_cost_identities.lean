-- Prove2me | Theorems.Thm_PoSUndirected_eq_1_4_cost_identities
-- name    : PoSUndirected.eq_1_4_cost_identities
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T08:00:39.888996+00:00
-- url     : https://prove2.me/theorems/0745700c-2cb8-4fda-8068-671463e549ba
-- title:
--   Equations (1) and (4) — the costs $E_d$ of the all-direct profile and $O_d$ of the floor tree
-- statement:
--   For every rational $0\le t<1$ and every depth $d\ge0$, in the host at $\eta(t)$, let $E_d$ be the cost of the all-direct profile (the total cost of all edges), $O_d$ the cost of the tree $T_d$, $G_d=\sum_{r=0}^{d-1}B_{\rm rec}^r$ and $\mathcal L=\mathcal L(\eta(t))=(S+C_\Sigma)/(S-\alpha)$. Then
--   $$
--   E_d=1+\frac{S+C_\Sigma}{\alpha}G_d,\qquad O_d=B_{\rm rec}^{d}+\frac{U_{\rm fix}}{\alpha}G_d,\tag{1}
--   $$
--   Moreover $\mathcal L>1$, $\mathcal LU_{\rm fix}-(S+C_\Sigma)=-\mathcal L\alpha(B_{\rm rec}-1)$ and $(B_{\rm rec}-1)G_d=B_{\rm rec}^d-1$, which give
--   $$
--   \mathcal LO_d-E_d=\mathcal L-1,\qquad \frac{E_d}{O_d}=\mathcal L-\frac{\mathcal L-1}{O_d},\qquad O_d\ge B_{\rm rec}^{d}.\tag{4}
--   $$
--
--   These identities turn the price of stability of the construction into $\mathcal L(\eta(t))$ minus an error that vanishes as the depth grows.
--
--   **Formalization Note** $E_d$ and $O_d$ are the actual costs in the depth-$d$ host, not numbers defined by the recursion of §A.4; the first clause of the statement identifies $E_d$ with the social cost of the all-direct profile.
--
--   Differences from the source:
--   - encoding: the parameters of the construction → $\eta(t)=(1-t)\eta_0+t\eta_1$ with $t$ rational and $0\le t<1$; reason: §A.5, p.18 (PDF p.20): "Throughout the construction use η(t) = (1 − t)η0 + tη1, where t is rational and 0 ≤ t < 1"
-- source:
--   Tsoufis, The Price of Stability in Undirected Network Design: Lower Bounds and Structural Guarantees (preprint, sha256 c095d811fa04b471d74ba4fdab8fb89ccb3d34079d3bf07384f46ac57144866c), equation (1), p.6 (PDF p.8); equation (4), p.18 (PDF p.20)

import Mathlib
import Definitions.Def_PoSUndirected_gadgetRegion

open CongestionPoA.AsymSum PriceOfStability.Harmonic

namespace PoSUndirected

open Params in
/-- Tsoufis (preprint, sha256 c095d811…), equation (1), p.6 (PDF p.8), and equation (4), p.18
(PDF p.20). In the construction at `η(t)`, `0 ≤ t < 1` rational, of depth `d`, with
`G_d = Σ_{r=0}^{d−1} B_rec^r` and `L = L(η) = (S + C_Σ)/(S − α)`: the all-direct profile costs
`E_d` (the total cost of the host), and
`E_d = 1 + ((S + C_Σ)/α)·G_d`, `O_d = B_rec^d + (U_fix/α)·G_d` (1), `L > 1`, the two identities
`L·U_fix − (S + C_Σ) = −L·α·(B_rec − 1)` and `(B_rec − 1)·G_d = B_rec^d − 1`, and `L·O_d − E_d = L − 1`,
`E_d/O_d = L − (L − 1)/O_d` and `O_d ≥ B_rec^d` (4).

**Formalization Note.** `E_d` and `O_d` are the actual costs of the all-direct profile and of
the tree `T_d` of the depth-`d` host (`Ed`, `Od`), not numbers defined by the recursion. The `L`
of (4) is `Params.Leta`, not the constant of Theorem 3.1. -/
theorem eq_1_4_cost_identities (t : ℚ) (ht0 : 0 ≤ t) (ht1 : t < 1) (d : ℕ) :
    designCost (fun e _ => (hostCost (etaAt t) e : ℝ)) (directProfile (E := HEdge d)) =
        (Ed (etaAt t) d : ℝ) ∧
    Ed (etaAt t) d = 1 + ((etaAt t).S + (etaAt t).CSigma) / (etaAt t).α * Gd (etaAt t) d ∧
    Od (etaAt t) d = (etaAt t).Brec ^ d + (etaAt t).Ufix / (etaAt t).α * Gd (etaAt t) d ∧
    1 < (etaAt t).Leta ∧
    (etaAt t).Leta * (etaAt t).Ufix - ((etaAt t).S + (etaAt t).CSigma) =
      -((etaAt t).Leta * (etaAt t).α * ((etaAt t).Brec - 1)) ∧
    ((etaAt t).Brec - 1) * Gd (etaAt t) d = (etaAt t).Brec ^ d - 1 ∧
    (etaAt t).Leta * Od (etaAt t) d - Ed (etaAt t) d = (etaAt t).Leta - 1 ∧
    Ed (etaAt t) d / Od (etaAt t) d = (etaAt t).Leta - ((etaAt t).Leta - 1) / Od (etaAt t) d ∧
    (etaAt t).Brec ^ d ≤ Od (etaAt t) d := by sorry

end PoSUndirected
