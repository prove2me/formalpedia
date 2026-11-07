-- Prove2me | Theorems.Thm_QuasiStrictNE_lemma_3
-- name    : QuasiStrictNE.lemma_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T13:11:09.043028+00:00
-- url     : https://prove2.me/theorems/1f54794d-e083-485d-95d8-ca5efffe827c
-- title:
--   Lemma 3 — rational relative-interior points by linear programming in polynomial time
-- statement:
--   For $F\in\mathcal C_m$ let
--   $$
--   I_F=\{i\in M : x_i>0 \text{ for some } x\in F\},\qquad J_F=\{j\in N : F\subseteq P_j\}.
--   $$
--   Given the game and these index sets, a rational point $p_F\in\mathrm{relint}\,F$ can be computed in polynomial time. The same holds for $G\in\mathcal C_n$ (with $I_G=\{j : y_j>0\text{ for some }y\in G\}$, $J_G=\{i : G\subseteq Q_i\}$).
--
--   Differences from the source:
--   - encoding: given the index sets IF, JF, compute pF in polynomial time → ∃ polynomial-time maps gP, gQ on bit strings: input = game code ++ characteristic vectors of the label sets (labelsP, labelsQ), output = encRatVec code of a rational point of intrinsicInterior ℝ F (IsLPSelection); reason: a string model of the paper's algorithm; one pair of maps for all games
-- source:
--   Hansen & Nie, On Existence and Computational Complexity of Quasi-strict Equilibria, arXiv:2611.06350 (preprint, sha256 c265dace…), Lemma 3, p.14

import Mathlib
import Definitions.Def_QuasiStrictNE_IsLPSelection

namespace QuasiStrictNE

/-- **Lemma 3** (Hansen & Nie, *On Existence and Computational Complexity of Quasi-strict Equilibria*,
arXiv:2611.06350, Lemma 3, p.14: "For F ∈ Cm, let IF = {i ∈ M : xi > 0 for some x ∈ F},
JF = {j ∈ N : F ⊆ Pj}. Given these index sets, a rational point pF ∈ relint F can be computed in
polynomial time. The same holds for G ∈ Cn").

There are polynomial-time maps `gP`, `gQ` that, for every rational bimatrix game with `m, n ≥ 1`,
compute from the game and the label sets `(I_F, J_F)` of a face `F ∈ Cm` a rational point of
`relint F`, and from the game and the label sets `(I_G, J_G)` of a face `G ∈ Cn` a rational point of
`relint G` (`IsLPSelection`).

**Formalization Note** One pair of maps serves all games (uniformity). The label sets are given as
characteristic bit vectors after the game code (`labelsP`, `labelsQ`); outputs are `encRatVec` codes. -/
theorem lemma_3 : ∃ gP gQ : List Bool → List Bool, IsLPSelection gP gQ := by sorry

end QuasiStrictNE
