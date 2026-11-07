-- Prove2me | Theorems.Thm_SNPTreedepth_ding_wqo
-- name    : SNPTreedepth.ding_wqo
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:27:07.755472+00:00
-- url     : https://prove2.me/theorems/b24eac86-9d3d-4ba2-a73a-327ef9c09003
-- title:
--   [Lop23, Fact 3.3.9] / [Din92] as used — bounded-treedepth structures are well-quasi-ordered by induced substructures (cited)
-- statement:
--   Fix a finite signature and an integer $h$. The class of finite relational structures over this signature of treedepth at most $h$ is well-quasi-ordered by the induced-substructure relation: for every infinite sequence $X_0,X_1,X_2,\dots$ of such structures there are indices $i<j$ such that
--   $$
--   X_i\ \text{is isomorphic to an induced substructure of}\ X_j .
--   $$
--
--   This is the consequence of Ding's theorem (J. Graph Theory 1992) recorded by Lopez (thesis 2023, Fact 3.3.9), cited by the paper; it is the input to Lemma 31.
--
--   Differences from the source:
--   - encoding: any class of finite relational structures over a fixed finite signature with bounded treedepth is well-quasi-ordered by the induced-substructure relation → every sequence of structures over σ on Fin n_m (n_m ≥ 1) with treedepth ≤ h has i < j with X_i embedding as an induced substructure of X_j; reason: definition of a well-quasi-order; every finite structure is isomorphic to one on some Fin n
-- source:
--   Depian, Ganian, Greilhuber, Gründel, Wietheger, A Uniform Algorithm for Strict NP on Bounded-Treedepth Structures, STOC 2027 submission (manuscript sha256 98e4e1a9…), p.30 (PDF p.31), citing [Lop23, Fact 3.3.9] and [Din92]

import Mathlib
import Definitions.Def_SNPTreedepth_Structure
import Definitions.Def_SNPTreedepth_treedepth

set_option autoImplicit false

namespace SNPTreedepth

/-- **[Lop23, Fact 3.3.9] / [Din92] as used** (Depian, Ganian, Greilhuber, Gründel, Wietheger, *A Uniform Algorithm for Strict NP on
Bounded-Treedepth Structures*, STOC 2027 submission (manuscript sha256 98e4e1a9…), p.30 (PDF p.31)): "By Lopez [Lop23, Fact
3.3.9], which records a consequence of the work of Ding [Din92], we have that any class of finite
relational structures over a fixed finite signature that has bounded treedepth is well-quasi-ordered
by the induced-substructure relation (see also Lopez [Lop22])." A cited external result
(G. Ding, *Subgraphs and well-quasi-ordering*, J. Graph Theory 16 (1992); C. Lopez, PhD thesis,
2023), stated as the paper uses it.

**Formalization Note** Well-quasi-ordered: every infinite sequence `X₀, X₁, …` of structures over
the signature `σ` (on `Fin n_m`, `n_m ≥ 1`) with treedepth at most `h` has indices `i < j` such that
`X_i` is isomorphic to an induced substructure of `X_j`. -/
theorem ding_wqo (σ : Signature) (h : ℕ) (n : ℕ → ℕ) (hn : ∀ m, 1 ≤ n m)
    (X : (m : ℕ) → Structure σ (Fin (n m))) (hX : ∀ m, td (X m) ≤ h) :
    ∃ i j : ℕ, i < j ∧ (X i).EmbedsInduced (X j) := by sorry

end SNPTreedepth
