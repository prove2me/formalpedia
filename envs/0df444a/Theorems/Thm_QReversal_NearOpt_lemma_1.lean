-- Prove2me | Theorems.Thm_QReversal_NearOpt_lemma_1
-- name    : QReversal.NearOpt.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T06:42:09.314982+00:00
-- url     : https://prove2.me/theorems/16bc06cd-3620-4d07-9b75-f890e7aebf7e
-- title:
--   Lemma 1, p. 7 — the reversal operation does not depend on the decomposition of A
-- statement:
--   Let $\mathcal A\sim\{A_i\}_{i\in\iota}$ and $\mathcal A\sim\{A'_j\}_{j\in\iota'}$ be two decompositions of the same completely positive map, i.e. $\sum_iA_iXA_i^\dagger=\sum_jA'_jXA_j'^\dagger$ for every matrix $X$. Let $\rho$ be a density matrix such that $\mathcal A(\rho)$ has full support. Then the reversal operations built from the two decompositions by (12) are the same map: for every matrix $Y$,
--   $$
--   \sum_i R_iYR_i^\dagger=\sum_j R'_jYR_j'^\dagger,\qquad R_i=\rho^{1/2}A_i^\dagger\mathcal A(\rho)^{-1/2},\quad R'_j=\rho^{1/2}A_j'^\dagger\mathcal A(\rho)^{-1/2}.
--   $$
--
--   This justifies the notation $\mathcal R_{\mathcal A,\rho}$, which refers only to the map $\mathcal A$; the proof of Theorem 3 uses it to change decompositions freely.
--
--   **Formalization Note** The two decompositions may have different index sets. The full-support hypothesis and the density-matrix hypothesis are the standing assumptions under which (12) is defined (pp. 6–7); the conclusion compares the two reversal families as maps.
-- source:
--   Barnum, Knill, Reversing quantum dynamics with near-optimal quantum and classical fidelity, arXiv:quant-ph/0004088v2, p. 7, Lemma 1

import Mathlib
import Definitions.Def_PeresTerno_kraus_basics
import Definitions.Def_QReversal_NearOpt_Setting

open Matrix PeresTerno
open scoped MatrixOrder ComplexOrder

namespace QReversal.NearOpt

theorem lemma_1 {n ι ι' : Type*} [Fintype n] [DecidableEq n] [Fintype ι] [Fintype ι']
    (A : ι → Matrix n n ℂ) (A' : ι' → Matrix n n ℂ)
    (hAA' : ∀ X : Matrix n n ℂ, krausUpdate A X = krausUpdate A' X)
    (ρ : Matrix n n ℂ) (hρ : IsDensityMatrix ρ) (hfull : (krausUpdate A ρ).PosDef) :
    ∀ Y : Matrix n n ℂ, krausUpdate (reversal A ρ) Y = krausUpdate (reversal A' ρ) Y := by sorry

end QReversal.NearOpt
