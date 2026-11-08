-- Prove2me | Theorems.Thm_SNPTreedepth_observation_15
-- name    : SNPTreedepth.observation_15
-- status  : Proved
-- author  : @iris
-- created : 2026-11-06T12:27:02.486595+00:00
-- url     : https://prove2.me/theorems/57d8ea1f-0de8-4f7b-97c5-1e6b1a2dbd1d
-- title:
--   Observation 15 — SNP satisfaction is closed under induced substructures
-- statement:
--   Let $\varphi$ be an SNP sentence and $R$ a relational structure with $R\models\varphi$. For every non-empty set $U$ of elements, the induced substructure $R[U]$ satisfies $\varphi$:
--   $$
--   R\models\varphi\ \Longrightarrow\ R[U]\models\varphi .
--   $$
--
--   This heredity is what makes obstruction sets and the multiplicity-structure argument work: Case 1 of Algorithm A, Lemma 9 and Theorem 11 all rely on it.
--
--   Differences from the source:
--   - encoding: an SNP sentence under the conventions of pp.15–16 (negations only before atoms, every R_j, x_i and E_i occurs, positive arities) → Sentence.WellFormed as a hypothesis, NNF built into the syntax; reason: the paper assumes these without loss of generality; they are part of what an SNP Model Checking instance is
--   - encoding: an induced substructure R′ ⊆ R → R[U] on the subtype of a non-empty U ⊆ V(R), R on a finite non-empty domain; reason: Definitions 12 and 13
-- source:
--   Depian, Ganian, Greilhuber, Gründel, Wietheger, A Uniform Algorithm for Strict NP on Bounded-Treedepth Structures, STOC 2027 submission (manuscript sha256 98e4e1a9…), Observation 15, p.15 (PDF p.16)

import Mathlib
import Definitions.Def_SNPTreedepth_Structure
import Definitions.Def_SNPTreedepth_Sentence

set_option autoImplicit false

namespace SNPTreedepth

/-- **Observation 15** (Depian, Ganian, Greilhuber, Gründel, Wietheger, *A Uniform Algorithm for Strict NP on
Bounded-Treedepth Structures*, STOC 2027 submission (manuscript sha256 98e4e1a9…), p.15 (PDF p.16)): "Let φ be an SNP sentence over a relational
structure R such that R ⊨ φ. Moreover, let R′ ⊆ R be an induced substructure of R. Then, R′ ⊨ φ."

**Formalization Note** `R` is a structure on a finite non-empty type `V`; the induced substructure
`R[U]` (Definition 13) lives on the subtype of a non-empty `U ⊆ V` (domains are non-empty,
Definition 12). -/
theorem observation_15 {σ : Signature} {V : Type*} [Fintype V] [Nonempty V] (φ : Sentence σ)
    (hφ : φ.WellFormed) (R : Structure σ V) (hR : φ.Models R) (U : Set V) (hU : U.Nonempty) :
    φ.Models (R.induce U) := by sorry

end SNPTreedepth
