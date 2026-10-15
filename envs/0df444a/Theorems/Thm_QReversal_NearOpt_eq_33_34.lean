-- Prove2me | Theorems.Thm_QReversal_NearOpt_eq_33_34
-- name    : QReversal.NearOpt.eq_33_34
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T06:42:17.012457+00:00
-- url     : https://prove2.me/theorems/633d4386-6212-4dd3-a3ef-f0f7f78edb18
-- title:
--   Proof of Theorem 3, lines (33)–(34), p. 9 — the final sum is at most tr R(A(ρ)) ≤ 1
-- statement:
--   Let $\mathcal A\sim\{A_i\}_i$ be trace-preserving, $E=\{p_l,\rho_l\}_l$ an ensemble of commuting density matrices with $\rho=\sum_lp_l\rho_l$, $\mathcal R\sim\{R_i\}_i$ trace-nonincreasing ($\sum_iR_i^\dagger R_i\le I$) and $\mathcal B\sim\{B_j\}_j$ any family, indexed by the same set as $\mathcal R$, with $\mathcal B(\rho)\le\mathcal A(\rho)$. Then
--   $$
--   \sum_lp_l\sum_{i,j}\operatorname{tr}R_iB_j\rho_lB_j^\dagger R_i^\dagger=\sum_lp_l\operatorname{tr}\mathcal R(\mathcal B(\rho_l))=\operatorname{tr}\mathcal R(\mathcal B(\rho))\le\operatorname{tr}\mathcal R(\mathcal A(\rho))\le1 .
--   $$
--
--   This closes the bound (27)–(34) that the proof of Theorem 3 needs in line (23).
--
--   **Formalization Note** The page prints the last step as $\operatorname{tr}\mathcal R(\mathcal A(\rho))=1$. After the replacement $R_i\mapsto P_CR_i$ in the proof, $\mathcal R$ is only trace-nonincreasing, so the correct step is $\le1$, which is what is stated. The paper uses $l$-dependent decompositions $R^l_i$, $B^l_j$ of the same maps $\mathcal R$, $\mathcal B$ in (32); since (33) depends only on the maps, the statement uses one decomposition of each. Traces of positive semidefinite matrices are real and are taken as real parts.
-- source:
--   Barnum, Knill, Reversing quantum dynamics with near-optimal quantum and classical fidelity, arXiv:quant-ph/0004088v2, p. 9, proof of Theorem 3, lines (33)–(34)

import Mathlib
import Definitions.Def_PeresTerno_kraus_basics
import Definitions.Def_QReversal_NearOpt_Setting

open Matrix PeresTerno
open scoped MatrixOrder ComplexOrder

namespace QReversal.NearOpt

theorem eq_33_34 {n L ι κ : Type*} [Fintype n] [DecidableEq n] [Fintype L] [Fintype ι]
    [Fintype κ]
    (A : ι → Matrix n n ℂ) (hA : IsTracePreserving A)
    (p : L → ℝ) (ρs : L → Matrix n n ℂ) (hE : IsCommutingEnsemble p ρs)
    (ρ : Matrix n n ℂ) (hρ : ρ = avgState p ρs)
    (R B : κ → Matrix n n ℂ) (hR : IsTraceNonincreasing R)
    (hBA : krausUpdate B ρ ≤ krausUpdate A ρ) :
    ∑ l, p l * ∑ i, ∑ j, (Matrix.trace (R i * B j * ρs l * (B j)ᴴ * (R i)ᴴ)).re =
        ∑ l, p l * (Matrix.trace (krausUpdate R (krausUpdate B (ρs l)))).re ∧
      ∑ l, p l * (Matrix.trace (krausUpdate R (krausUpdate B (ρs l)))).re =
        (Matrix.trace (krausUpdate R (krausUpdate B ρ))).re ∧
      (Matrix.trace (krausUpdate R (krausUpdate B ρ))).re ≤
        (Matrix.trace (krausUpdate R (krausUpdate A ρ))).re ∧
      (Matrix.trace (krausUpdate R (krausUpdate A ρ))).re ≤ 1 := by sorry

end QReversal.NearOpt
