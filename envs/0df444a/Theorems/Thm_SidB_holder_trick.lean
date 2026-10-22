-- Prove2me | Theorems.Thm_SidB_holder_trick
-- name    : SidB.holder_trick
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-21T21:25:37.284684+00:00
-- url     : https://prove2.me/theorems/7ec18221-8b5c-4e66-a8b6-8329b7af5ea6
-- title:
--   The Hoelder trick: homomorphism densities dominate weighted downset densities (Theorem 4.1)
-- statement:
--   The first part of Theorem 4.1 of the paper, the Hoelder trick. Let H be a bipartite graph with left part A and maximum right degree r, let d_k be the number of right vertices of degree k, and let the symmetric weight vector alpha be given by alpha_k = d_k / C(|A|, k). Then for every graphon W the alpha-weighted homomorphism density of the (|A|, r)-downset graph is at most the homomorphism density of H: t_J^alpha(W) <= t_H(W). The proof attaches to each subset I of A the functional f_I = rho(x_I)^{c_I}, c_I the number of right vertices with neighbourhood exactly I; the symmetrized functional f~_I equals rho(x_I)^{alpha_{|I|}}; and Hoelder's inequality (1) over the permutations of A compares the downset density with t_H(W) itself. In the mission the inequality is stated with the weight vector given by the hypothesis halpha: the alpha-weighted downset density at |A| and the maximum degree is at most the density of H.
--
--   **Formalization Note** The divisibility hypothesis that makes alpha integral in the application to Theorem 1.1 is carried by the statement only through the weight hypothesis; the symmetrization runs on the transport axiom and the Hoelder axiom of the graphon interface.
-- source:
--   D. Conlon, J. Lee, Sidorenko's conjecture for blow-ups, Discrete Anal. 2021:2 (2021), Section 4 (Theorem 4.1, first part, pages 8-9).

import Mathlib
import Definitions.Def_SidB_graph
import Definitions.Def_SidB_hyper

namespace SidB

/-!  Milestone 2 (Theorem 4.1, first half): the Hoelder trick. Let H be a
bipartite graph with left part A and maximum right degree r, and let the
symmetric weight vector alpha be given by alpha_k = d_k / C(|A|, k), where
d_k is the number of right vertices of degree k. Then for every graphon the
alpha-weighted homomorphism density of the (|A|, r)-downset graph is at
most the homomorphism density of H. The proof symmetrizes the rho-power
functionals over the permutations of the left part and applies the Hoelder
axiom; the divisibility hypothesis is what makes alpha integral, so that
the weighted downset density is the one to which the weighted Sidorenko
theorem (milestone 6) applies. -/
theorem holder_trick (g : Graphon) {A B : Type} [Fintype A] [Fintype B] (H : Bigraph A B)
    (α : ℕ → ℝ)
    (hα : ∀ k, 1 ≤ k → k ≤ H.maxDeg → α k = (H.degCount k : ℝ) / (Fintype.card A).choose k) :
    g.downsetDens (Fintype.card A) H.maxDeg α ≤ g.dens H := by sorry

end SidB
