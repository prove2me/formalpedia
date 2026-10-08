-- Prove2me | Theorems.Thm_QLLL_QSAT_finrank_inf_liftL_liftR
-- name    : QLLL.QSAT.finrank_inf_liftL_liftR
-- status  : Proved
-- author  : @sattath
-- created : 2026-10-06T17:45:59.398472+00:00
-- url     : https://prove2.me/theorems/0ef99b86-d4f8-4769-b935-453529e1f780
-- title:
--   Product rule for dimensions: $\dim\big((Y \otimes \mathbb{C}^B) \cap (\mathbb{C}^A \otimes W)\big) = \dim Y \cdot \dim W$
-- statement:
--   Let $A$ and $B$ be finite sets, and identify $\mathbb{C}^A \otimes \mathbb{C}^B$ with $\mathbb{C}^{A \times B}$. For a subspace $Y \subseteq \mathbb{C}^A$ let $\mathrm{lift}_L(Y)$ be the functions $f : A \times B \to \mathbb{C}$ all of whose column slices $f(\cdot, b)$ lie in $Y$, and for $W \subseteq \mathbb{C}^B$ let $\mathrm{lift}_R(W)$ be the functions all of whose row slices $f(a, \cdot)$ lie in $W$. Then
--   $$\dim\big(\mathrm{lift}_L(Y) \cap \mathrm{lift}_R(W)\big) \ =\ \dim Y \cdot \dim W.$$
--
--   This is the dimension count in the proof of Lemma 11 of Ambainis, Kempe and Sattath, $\dim(\pi \otimes \bigcap_i \pi_i) = \dim \pi \cdot \dim \bigcap_i \pi_i$, in the function model of the qubit space. It yields the mutual R-independence of constraints acting on disjoint qubits.
-- source:
--   A. Ambainis, J. Kempe, O. Sattath, A Quantum Lovász Local Lemma, J. ACM 59(5):24 (2012), arXiv:0911.1696 (numbering of the arXiv version), proof of Lemma 11 (dimension of a tensor product of subspaces)

import Definitions.Def_QLLL_LocalLemma_Basic
import Definitions.Def_QLLL_Quantum_KQSAT_Basic
import Mathlib

open QLLL
open QLLL.QSAT
open Finset Module
variable {n : ℕ}
open scoped Kronecker
variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
omit [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

theorem QLLL.QSAT.finrank_inf_liftL_liftR [Finite A] [Finite B]
    (Y : Submodule ℂ (A → ℂ)) (W : Submodule ℂ (B → ℂ)) :
    Module.finrank ℂ ((liftL Y ⊓ liftR W : Submodule ℂ ((A × B) → ℂ)))
      = Module.finrank ℂ Y * Module.finrank ℂ W := by sorry
