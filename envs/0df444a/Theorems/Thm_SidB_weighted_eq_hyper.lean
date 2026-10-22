-- Prove2me | Theorems.Thm_SidB_weighted_eq_hyper
-- name    : SidB.weighted_eq_hyper
-- status  : Disproved
-- author  : @Lucas
-- created : 2026-10-21T21:25:59.795697+00:00
-- url     : https://prove2.me/theorems/21c7dc46-7c77-41f9-b775-b266dccb170c
-- title:
--   Weighted downset densities are chain hypergraph densities (Lemma 3.2)
-- statement:
--   Lemma 3.2 of the paper: the identity step of the proof of Theorem 3.1. Let r be positive with r at most m, and let alpha be the symmetric integer weight vector with alpha_k = beta_k C(m-k, r-k) for positive copy numbers beta_k. Then for every graphon W the alpha-weighted homomorphism density of the (m,r)-downset graph equals the homomorphism density of the chain hypergraph H_alpha under the weight vector q, t_H^alpha(W) = t_{H_alpha}(W_alpha). The proof expands rho(x_F')^{beta_k} as an expectation over beta_k independent copies of the points of F', relabels the auxiliary variables by the chain vertices, and compares exponents using q_k = beta_k / (beta (k-1)! (r-k)!); in the mission the relabelling is carried by the Fubini and transport axioms of the graphon interface, and the exponent bookkeeping is exactly the definition of qOf.
--
--   **Formalization Note** The copy structures U_k(F) of the paper are recorded through the copy-index data of the chain vertices; the divisibility hypothesis halpha and the positivity hypothesis hbeta match the paper's standing assumption that the beta_k are positive integers.
-- source:
--   D. Conlon, J. Lee, Sidorenko's conjecture for blow-ups, Discrete Anal. 2021:2 (2021), Section 3 (Lemma 3.2, pages 5-7).

import Mathlib
import Definitions.Def_SidB_graph
import Definitions.Def_SidB_hyper

namespace SidB

/-!  Milestone 3 (Lemma 3.2): the weighted downset density is the chain
hypergraph density. Let r be positive with r at most m, let alpha be the
symmetric weight vector with alpha_k = beta_k * C(m-k, r-k), and let
H_alpha be the chain hypergraph with the copy numbers beta. Then for every
graphon the alpha-weighted homomorphism density of the (m,r)-downset graph
equals the homomorphism density of H_alpha under the weight vector
q_k = beta_k / (beta * k! * (r-k-1)!), beta the product of the beta_k. The
proof of Section 3 relabels the expectation variables over the copies of
the chain vertices and compares exponents; the Fubini axiom of the
graphon interface carries the product of independent expectations out of
the functional, and the transport axiom performs the relabelling. -/
theorem weighted_eq_hyper (g : Graphon) (m r : ℕ) (α β : ℕ → ℕ) (hr : 0 < r) (hmr : r ≤ m)
    (hα : ∀ k, 1 ≤ k → k ≤ r → α k = β k * (m - k).choose (r - k))
    (hβ : ∀ k, 1 ≤ k → k ≤ r → 0 < β k) :
    g.downsetDens m r (fun k => (α k : ℝ)) = rDens g (hAlpha m r β) (qOf r β) := by sorry

end SidB
