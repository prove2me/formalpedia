-- Prove2me | Theorems.Thm_QThermalClassical_lemma_10
-- name    : QThermalClassical.lemma_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T23:13:37.858185+00:00
-- url     : https://prove2.me/theorems/1ffb0b50-5ef1-46a6-a01b-eeb331f59b5c
-- title:
--   Lemma 10 — Hermitian monomials are $0$ or signed Pauli strings
-- statement:
--   Every Hermitian monomial $X$ (Definition 3.1) is either $0$ or a signed Pauli string:
--   $$
--   X\in\{0\}\cup\{\pm P:\ P\in\mathcal P^{\otimes n}\}\qquad(80).
--   $$
--
--   This is what makes each factor $I+c_iX_i$ of the final configuration a factor of the form handled by Lemma 7.
--
--   Differences from the source:
--   - generalization: $E_1,E_2$ Pauli products up to a phase returned by the sampling primitive → any Pauli products up to a phase; reason: the proof uses only that they are Pauli products with phases in $\{\pm1,\pm i\}$; this covers the primitive's outputs and the adjoints used in Algorithm 1
--   - encoding: a Hermitian monomial → an inductive predicate on pairs $(X,C(X))$ built from $(I,())$ by (76) and (79); reason: Definition 3.1; the identity is the empty Pauli product
-- source:
--   J. Cotler, H. Putterman, A. Zlokapa, When quantum thermal states look classical, arXiv:2607.28536 (held version, sha256 7491d0b2…), Lemma 10, eq. (80), p.25

import Mathlib
import Definitions.Def_QThermalClassical_IsHermitianMonomial

set_option autoImplicit false

namespace QThermalClassical

/-- **Lemma 10.** A Hermitian monomial is either `0` or a signed Pauli product:
`X ∈ {0} ∪ {±P : P ∈ P^{⊗n}}`.

Source: J. Cotler, H. Putterman, A. Zlokapa, *When quantum thermal states look classical*,
arXiv:2607.28536 (held version, sha256 7491d0b2…), Lemma 10, eq. (80), p.25.

**Formalization Note.** `P^{⊗n}` is the set of Pauli strings `pauliOp P` of Pauli words
(including the identity word). -/
theorem lemma_10 {Q : Type} [Fintype Q] [DecidableEq Q] (X : Op Q) (C : List (PauliWord Q))
    (hX : IsHermitianMonomial X C) :
    X = 0 ∨ ∃ P : PauliWord Q, X = pauliOp P ∨ X = -pauliOp P := by sorry

end QThermalClassical
