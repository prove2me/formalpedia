-- Prove2me | Theorems.Thm_QLLL_QSAT_relDim_lift
-- name    : QLLL.QSAT.relDim_lift
-- status  : Proved
-- author  : @sattath
-- created : 2026-10-06T17:46:04.47299+00:00
-- url     : https://prove2.me/theorems/04949470-aaba-456d-a468-9ceb98f5c84d
-- title:
--   Relative dimension of a lifted local subspace: $\mathrm{R}(\mathrm{lift}_S(Y)) = \dim Y / 2^{|S|}$
-- statement:
--   Model the state space of $n$ qubits as $\mathcal{H}_n = \mathbb{C}^{\{0,1\}^n}$, the functions from bit strings to $\mathbb{C}$, and write $\mathrm{R}(X) = \dim X / 2^n$ for the relative dimension of a subspace $X \subseteq \mathcal{H}_n$. For a set $S$ of qubits and a subspace $Y$ of the local space $\mathbb{C}^{\{0,1\}^S}$, let $\mathrm{lift}_S(Y) \subseteq \mathcal{H}_n$ be the space of states all of whose $S$-slices (obtained by fixing the bits outside $S$) lie in $Y$; in tensor language this is $Y \otimes \mathbb{C}^{\{0,1\}^{S^c}}$. Then
--   $$\mathrm{R}\big(\mathrm{lift}_S(Y)\big) \ =\ \frac{\dim Y}{2^{|S|}}.$$
--
--   In words, extending a local constraint to all qubits does not change its relative dimension. This converts the local hypotheses of the $k$-QSAT corollary (dimension of each local satisfying space) into the relative-dimension hypotheses of the quantum local lemma.
--
--   **Formalization Note** Qubits are modelled as functions on bit strings; the denominator is written as the number of bit strings on $S$, which equals $2^{|S|}$.
-- source:
--   A. Ambainis, J. Kempe, O. Sattath, A Quantum Lovász Local Lemma, J. ACM 59(5):24 (2012), arXiv:0911.1696 (numbering of the arXiv version), Lemma 8 (relative dimension is preserved under tensoring with the full space), as used in Corollary 16

import Definitions.Def_QLLL_LocalLemma_Basic
import Definitions.Def_QLLL_Quantum_KQSAT_Basic
import Mathlib

open QLLL
open QLLL.QSAT
open Finset Module
variable {n : ℕ}

theorem QLLL.QSAT.relDim_lift (S : Finset (Fin n)) (Y : Submodule ℂ (HIn S)) :
    relDim (lift S Y) = (Module.finrank ℂ Y : ℝ) / (Fintype.card (CfgIn S) : ℝ) := by sorry
