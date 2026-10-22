-- Prove2me | Theorems.Thm_QMaxCutBeyond_TwoQubit_eq_26
-- name    : QMaxCutBeyond.TwoQubit.eq_26
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T13:39:09.426041+00:00
-- url     : https://prove2.me/theorems/c10b84fd-e93d-49e9-bcf6-1fd6bb7b3064
-- title:
--   Eq. (26) — for a forest F ⊆ E some basis state has energy ≥ Σ_{e∈F} w_e
-- statement:
--   Let $G=(V,E,w)$ have nonnegative weights and let $F\subseteq E$ be a forest. There is a computational basis state $|s\rangle$, $s\in\{0,1\}^n$, with
--   $$\langle s|H_G|s\rangle\;\ge\;f,\qquad f=\sum_{e\in F}w_e .$$
--
--   This is the first (classical) candidate state of eq. (27).
--
--   **Formalization Note** Only existence is stated; "we may efficiently compute" is not formalized.
-- source:
--   Anshu, Gosset & Morenz, Beyond product state approximations for a quantum analogue of Max Cut, arXiv:2003.14394v1, p. 11, eq. (26), proof of Theorem 3

import Mathlib
import Definitions.Def_QMaxCutBeyond_TwoQubit_Setting

namespace QMaxCutBeyond.TwoQubit

/-- Eq. (26), p. 11 (existence part): if `F ⊆ E` is a forest, some computational basis state
`|s⟩` has `⟨s|H_G|s⟩ ≥ f = Σ_{e∈F} w_e`. -/
theorem eq_26 {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (w : Sym2 (Fin n) → ℝ) (hw : ∀ e, 0 ≤ w e)
    (F : Finset (Sym2 (Fin n))) (hFG : F ⊆ G.edgeFinset)
    (hF : (SimpleGraph.fromEdgeSet (F : Set (Sym2 (Fin n)))).IsAcyclic) :
    ∃ s : Config n, ∑ e ∈ F, w e ≤ energy (hamiltonian G w) (basisState s) := by sorry

end QMaxCutBeyond.TwoQubit
