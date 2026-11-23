-- Prove2me | Theorems.Thm_SharedVehicleApprox_Pricing_Supplement_lemma_33
-- name    : SharedVehicleApprox.Pricing.Supplement.lemma_33
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T18:40:34.337227+00:00
-- url     : https://prove2.me/theorems/d070a1dc-b2e3-4fe3-aaca-4c53cc965084
-- title:
--   Lemma 33, p. 40 — raising point quantiles does not reduce any flow (corrected: strongly connected demand graph)
-- statement:
--   Consider the $m$-unit system with instantaneous rides and arrival rates $\varphi_{ij}\ge0$ whose graph $\{(i,j):i\ne j,\ \varphi_{ij}>0\}$ is strongly connected. Let $q,\tilde q\in[0,1]^n$ be point quantiles with $q_k\le\tilde q_k$ for every $k$, and let $\pi$, $\tilde\pi$ be stationary laws under them. Then, for every pair $(i,j)$,
--
--   $$f_{ij,m}(q)\le f_{ij,m}(\tilde q),$$
--
--   where $f_{ij,m}$ is the steady-state rate (3) of realized trips from $i$ to $j$.
--
--   Without prices this is what allows the thinned policy of the relaxation to be replaced by one that serves every customer, in the proof of Theorem 34.
--
--   **Formalization Note** Zero quantiles are allowed. For positive quantiles the stationary law is the product-form law of the Gordon–Newell network, and the flow is $A_{i,m}\varphi_{ij}q_i$.
--
--   Differences from the source:
--   - correction: no connectivity hypothesis (p. 7 treats the stationary law as unique; App. A assumes φ strongly connected) → the graph of φ is strongly connected; reason: false without it: n = 2, m = 1, φ = identity, q = q̃ = (1, 1); with the unit at node 1 under q and at node 2 under q̃, f_11 drops from 1 to 0. Excluded: demand graphs that are not strongly connected
--   - reading: vectors of point quantiles → all vectors in [0, 1]^n, zeros included; reason: §2.2 takes quantiles in [0, 1]; this is not the weaker reading of Definition 1’s positive service rates
--   - encoding: the steady-state distribution, treated as unique (p. 7) → any probability vector on the finite state space that satisfies the balance equations; reason: the balance equations are the paper’s characterization of stationarity, and quantifying over all laws avoids assuming uniqueness
--   - generalization: the positive population and node counts of the vehicle-system setting → natural-number counts, including zero where the other hypotheses are satisfiable; reason: every positive source instance is retained. At m = 0 the only state is the zero-count state and objectives and flows are zero; at n = 0 and m > 0 no normalized stationary law exists. The availability maximum is used only with an explicit nonempty node type
-- source:
--   Banerjee, Freund & Lykouris, Pricing and Optimization in Shared Vehicle Systems: An Approximation Framework, arXiv:1608.06819v4, p. 40 (PDF 41), Lemma 33

import Mathlib
import Definitions.Def_QueueingFundamentals_Networks_ClosedJackson
import Definitions.Def_SharedVehicleApprox_Pricing_Model
import Definitions.Def_SharedVehicleApprox_Pricing_Supplement_PointPricing

open Finset QueueingFundamentals.Networks

namespace SharedVehicleApprox.Pricing.Supplement

/-- Lemma 33, p. 40 (corrected: the graph `{(i, j) : φ_ij > 0}` is strongly connected): raising
point quantiles does not decrease the steady-state rate of realized trips between any pair of
nodes. -/
theorem lemma_33 {n m : ℕ} (φ : Fin n → Fin n → ℝ) (hφ : ∀ i j, 0 ≤ φ i j)
    (hconn : SupportConnected φ (fun _ _ => 1))
    (q qt : Fin n → ℝ) (hq : ∀ i, 0 ≤ q i ∧ q i ≤ 1) (hqt : ∀ i, 0 ≤ qt i ∧ qt i ≤ 1)
    (hle : ∀ k, q k ≤ qt k)
    (π πt : (Fin n → ℕ) → ℝ)
    (hπ : IsStationary n m φ (toPolicy (pointQuantile q)) π)
    (hπt : IsStationary n m φ (toPolicy (pointQuantile qt)) πt) (i j : Fin n) :
    flow n m φ (toPolicy (pointQuantile q)) π i j ≤
      flow n m φ (toPolicy (pointQuantile qt)) πt i j := by sorry

end SharedVehicleApprox.Pricing.Supplement
