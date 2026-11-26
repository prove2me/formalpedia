-- Prove2me | Theorems.Thm_SingleExpBisect_Main_dp_state_support_and_coeff_bounds
-- name    : SingleExpBisect.Main.dp_state_support_and_coeff_bounds
-- status  : Proved
-- author  : @Soh Kumabe
-- created : 2026-11-26T10:17:46.287737+00:00
-- url     : https://prove2.me/theorems/0f9cffdc-46bf-5d5d-893b-c369dc9968ec
-- title:
--   Sparse cut DP state bounds — number of monomials and coefficient size in the transitions of Lemmas 3.4–3.6
-- statement:
--   For a graph with n vertices, a cut budget k and a boundary D, each of the two cut polynomials after the boundary substitution has at most (n+1)(k+1)2^|D| monomials. Every coefficient is an integer between 0 and 2^n. For a bag pattern S of at most 2k vertices, the truncated boundary substitution of its logarithmic slice has at most (n+1)(k+1)2^(4k) nonzero coefficients. These bounds apply respectively to the output states in Lemmas 3.5–3.6 and Lemma 3.4.
-- source:
--   Kumabe, Single-Exponential FPT Algorithms for Minimum Bisection and Matching Cut via a New Unbreakable Decomposition, arXiv:2611.05982 (October 2026 version; PDF SHA256 6530ce94…6b76541), §3.3, p. 20, Lemma 3.4

import Mathlib
import Definitions.Def_SingleExpBisect_Main_NodeData
open scoped Classical

namespace SingleExpBisect.Main
open MinBisectFPT
theorem dp_state_support_and_coeff_bounds {n : ℕ} (G : SimpleGraph (Fin n)) (W B D : Finset (Fin n)) (k : ℕ) :
    (∀ P ∈ ({omega D (Zfull G W k), omega D (Zle G W B k)} : Finset (MvPolynomial (Var n) ℚ)),
      P.support.card ≤ 2^D.card * (n+1) * (k+1) ∧
      ∀ e, ∃ j : ℕ, j ≤ 2^n ∧ MvPolynomial.coeff e P = (j : ℚ)) ∧
    ∀ S ⊆ B, S.card ≤ 2*k →
      ∃ E : Finset (Var n →₀ ℕ), E.card ≤ (n+1)*(k+1)*2^(4*k) ∧
        ∀ e, MvPowerSeries.coeff e (truncKNB k n B (renamePS (omegaVar B) (LtS G W B k S))) ≠ 0 → e ∈ E := by sorry
end SingleExpBisect.Main
