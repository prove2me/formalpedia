-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P62_assisted_independence_monotonicity
-- name    : QAlgorithms.Papers.Independent.Information100.P62.assisted_independence_monotonicity
-- status  : Proved
-- author  : @fizzyinc3
-- created : 2026-10-19T07:24:31.816366+00:00
-- url     : https://prove2.me/theorems/295d1371-8fc9-4034-8fdc-f48edead7e6f
-- title:
--   Lemma 2.12, assisted part: independence number under graph homomorphisms
-- statement:
--   Let $S\subseteq M_I(\mathbb C)$ and $T\subseteq M_J(\mathbb C)$ be operator systems on nonzero finite-dimensional spaces. Suppose there is a finite ancillary space $E$ and an isometry $V:\mathbb C^I\to\mathbb C^J\otimes E$ such that
--
--   $$V^*(T\otimes L(E))V\subseteq S.$$
--
--   Then their entanglement-assisted independence numbers satisfy
--
--   $$\alpha_{\mathrm{ea}}(S)\le\alpha_{\mathrm{ea}}(T).$$
--
--   Here the independence number optimizes the number of exactly distinguishable messages over all finite shared states and finite ancillary spaces, with isometric encodings and Hilbert–Schmidt orthogonality against the operator system. This is the assisted component of Lemma 2.12 and the remaining prerequisite in the accompanying reduction of that lemma.
-- source:
--   Salzmann–Singh, Transmitting algebras through quantum channels, arXiv:2609.40054v1, PDF p. 16, Lemma 2.12 (entanglement-assisted inequality). https://arxiv.org/abs/2609.40054v1

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P62

noncomputable section
open QAlgorithms QAlgorithms.Papers.Independent.Information100.P62

theorem QAlgorithms.Papers.Independent.Information100.P62.assisted_independence_monotonicity {I J : Type} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] [Nonempty I] [Nonempty J]
    (S : Submodule ℂ (Matrix I I ℂ)) (T : Submodule ℂ (Matrix J J ℂ))
    (hS : IsSystem S) (hT : IsSystem T) (h : GraphHom S T) :
    alphaEA S ≤ alphaEA T := by sorry
