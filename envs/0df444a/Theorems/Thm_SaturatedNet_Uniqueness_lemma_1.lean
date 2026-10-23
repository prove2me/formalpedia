-- Prove2me | Theorems.Thm_SaturatedNet_Uniqueness_lemma_1
-- name    : SaturatedNet.Uniqueness.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T12:37:35.079007+00:00
-- url     : https://prove2.me/theorems/d5e005c5-41de-425d-8812-d347aaa73e6f
-- title:
--   Lemma 1, p. 25 — a subinvariant vector with strict slack reachable from every node forces ρ(P) < 1
-- statement:
--   Let $P \in \mathbb R_+^{n \times n}$ be a nonnegative square matrix and $\mathcal G_P$ its digraph
--   (link $i \to j$ when $P_{ij} \ne 0$). Suppose that
--
--   1. there is a nonnegative vector $v \ne 0$ with $Pv \le v$ (entrywise), and
--   2. for every node $i$ there is a path in $\mathcal G_P$ from $i$ to some node $j$ with
--      $(Pv)_j < v_j$.
--
--   Then
--
--   $$\rho(P) < 1.$$
--
--   The lemma is the tool of the appendix proof of Proposition 3: a positive subinvariant vector that is
--   strictly subinvariant somewhere downstream of every node certifies a spectral radius below one.
--
--   **Formalization Note.** The same $v$ serves both conditions. Paths may have length zero (the node
--   $i$ itself may be the node $j$), as in the paper's proof, where $l_i = 0$ is allowed.
-- source:
--   Massai, Como & Fagnani, Equilibria and Systemic Risk in Saturated Networks, arXiv:1912.04815v2, p. 25, Appendix, Lemma 1

import Mathlib
import Definitions.Def_SaturatedNet_Uniqueness_Model
open Matrix

namespace SaturatedNet.Uniqueness

theorem lemma_1 {n : Type*} [Fintype n] [DecidableEq n]
    (P : Matrix n n ℝ) (hP : ∀ i j, 0 ≤ P i j) (v : n → ℝ) (hv0 : 0 ≤ v) (hv : v ≠ 0)
    (hPv : P *ᵥ v ≤ v) (hpath : ∀ i, ∃ j, Reaches P i j ∧ (P *ᵥ v) j < v j) :
    specRad P < 1 := by sorry

end SaturatedNet.Uniqueness
