-- Prove2me | Theorems.Thm_QReversal_NearOpt_eq_14_15
-- name    : QReversal.NearOpt.eq_14_15
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T06:42:16.40384+00:00
-- url     : https://prove2.me/theorems/d22839e5-451a-4306-9744-776f7141d224
-- title:
--   Proof of Theorem 3, (14)–(15), p. 7 — restricting R to the support of ρ and the bound B(ρ) ≤ A(ρ)
-- statement:
--   Let $E=\{p_l,\rho_l\}_l$ be an ensemble of commuting density matrices with average $\rho=\sum_lp_l\rho_l$, and let $\mathcal A\sim\{A_i\}_i$ be such that $\mathcal A(\rho)$ has full support. Let $\mathcal R\sim\{R_k\}_k$ be trace-preserving and $P_C$ the projector onto the support of $\rho$. Put
--   $$
--   R'_k=P_CR_k,\qquad B_k=\mathcal A(\rho)^{1/2}R_k'^\dagger\rho^{-1/2},
--   $$
--   with $\rho^{-1/2}$ the generalized inverse square root. Then:
--
--   1. replacing $R_k$ by $R'_k$ does not change the average entanglement fidelity: $\bar F_e(E,\mathcal R'\mathcal A)=\bar F_e(E,\mathcal R\mathcal A)$;
--   2. $\mathcal R'$ is trace-nonincreasing: $\sum_kR_k'^\dagger R'_k\le I$;
--   3. (14) $R'_k=\rho^{1/2}B_k^\dagger\mathcal A(\rho)^{-1/2}$ for every $k$;
--   4. (15) $\mathcal B(\rho)\le\mathcal A(\rho)$, where $\mathcal B\sim\{B_k\}_k$.
--
--   These are the opening reductions of the proof of Theorem 3: every recovery is rewritten in the same shape as the reversal operation, with $B_k$ in place of $A_k$, and the inequality (15) is what bounds the final sum in (34).
--
--   **Formalization Note** $\mathcal B$ need not be trace-preserving. Part 1 needs no commutation; the commuting-ensemble hypothesis is the standing assumption of Theorem 3. Part 3 uses the full support of $\mathcal A(\rho)$.
-- source:
--   Barnum, Knill, Reversing quantum dynamics with near-optimal quantum and classical fidelity, arXiv:quant-ph/0004088v2, p. 7, proof of Theorem 3, (14)–(15)

import Mathlib
import Definitions.Def_PeresTerno_kraus_basics
import Definitions.Def_QReversal_NearOpt_Setting

open Matrix PeresTerno
open scoped MatrixOrder ComplexOrder

namespace QReversal.NearOpt

theorem eq_14_15 {n L ι κ : Type*} [Fintype n] [DecidableEq n] [Fintype L] [Fintype ι]
    [Fintype κ]
    (A : ι → Matrix n n ℂ) (p : L → ℝ) (ρs : L → Matrix n n ℂ)
    (hE : IsCommutingEnsemble p ρs) (ρ : Matrix n n ℂ) (hρ : ρ = avgState p ρs)
    (hfull : (krausUpdate A ρ).PosDef)
    (R : κ → Matrix n n ℂ) (hR : IsTracePreserving R) :
    let R' : κ → Matrix n n ℂ := fun k => supportProj ρ * R k
    let B : κ → Matrix n n ℂ := fun k => CFC.sqrt (krausUpdate A ρ) * (R' k)ᴴ * invSqrt ρ
    Fbar p ρs (comp R' A) = Fbar p ρs (comp R A) ∧
    IsTraceNonincreasing R' ∧
    (∀ k, R' k = CFC.sqrt ρ * (B k)ᴴ * invSqrt (krausUpdate A ρ)) ∧
    krausUpdate B ρ ≤ krausUpdate A ρ := by sorry

end QReversal.NearOpt
