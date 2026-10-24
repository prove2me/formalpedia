-- Prove2me | Theorems.Thm_QReversal_NearOpt_theorem_3
-- name    : QReversal.NearOpt.theorem_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T06:42:27.527466+00:00
-- url     : https://prove2.me/theorems/7490fe67-fb78-4fbd-be50-df8fee1501af
-- title:
--   Theorem 3, p. 7 — for commuting ensembles the reversal operation's average entanglement fidelity is at least the square of any recovery's
-- statement:
--   Let $\mathcal A\sim\{A_i\}_i$ be a trace-preserving completely positive map on a finite-dimensional system. Let $E=\{p_l,\rho_l\}_l$ be an ensemble of commuting density matrices — weights $p_l\ge0$ with $\sum_lp_l=1$, density matrices $\rho_l$ with $\rho_l\rho_{l'}=\rho_{l'}\rho_l$ — and let $\rho=\sum_lp_l\rho_l$. Assume $\mathcal A(\rho)$ has full support, and let $\mathcal R_{\mathcal A,\rho}\sim\{\rho^{1/2}A_i^\dagger\mathcal A(\rho)^{-1/2}\}_i$ be the reversal operation. Then for every trace-preserving completely positive map $\mathcal R\sim\{R_k\}_k$,
--   $$
--   \bar F_e(E,\mathcal R_{\mathcal A,\rho}\mathcal A)\;\ge\;\bar F_e(E,\mathcal R\mathcal A)^2,
--   $$
--   where $\bar F_e(E,\mathcal K)=\sum_lp_l\sum_k|\operatorname{tr}K_k\rho_l|^2$ is the average entanglement fidelity.
--
--   Consequently, if the best recovery has average entanglement fidelity $1-\eta$, the reversal operation, which is computed from $\mathcal A$ and $\rho$ alone, achieves at least $(1-\eta)^2\ge1-2\eta$: its error is at most twice the optimal error.
--
--   **Formalization Note** The recovery $\mathcal R$ ranges over every finite family $\{R_k\}_k$ with $\sum_kR_k^\dagger R_k=I$, over every finite index type. Trace preservation of $\mathcal A$ is the paper's noise model (§II); full support of $\mathcal A(\rho)$ is the standing assumption under which (12) is defined (p. 7). This is the statement of arXiv v2; the published J. Math. Phys. version proves it only for single states (Acknowledgments, p. 14).
-- source:
--   Barnum, Knill, Reversing quantum dynamics with near-optimal quantum and classical fidelity, arXiv:quant-ph/0004088v2, p. 7, Theorem 3, (13)

import Mathlib
import Definitions.Def_PeresTerno_kraus_basics
import Definitions.Def_QReversal_NearOpt_Setting

open Matrix PeresTerno
open scoped MatrixOrder ComplexOrder

namespace QReversal.NearOpt

theorem theorem_3 {n L ι : Type*} [Fintype n] [DecidableEq n] [Fintype L] [Fintype ι]
    (A : ι → Matrix n n ℂ) (hA : IsTracePreserving A)
    (p : L → ℝ) (ρs : L → Matrix n n ℂ) (hE : IsCommutingEnsemble p ρs)
    (ρ : Matrix n n ℂ) (hρ : ρ = avgState p ρs) (hfull : (krausUpdate A ρ).PosDef)
    {κ : Type*} [Fintype κ] (R : κ → Matrix n n ℂ) (hR : IsTracePreserving R) :
    Fbar p ρs (comp R A) ^ 2 ≤ Fbar p ρs (comp (reversal A ρ) A) := by sorry

end QReversal.NearOpt
