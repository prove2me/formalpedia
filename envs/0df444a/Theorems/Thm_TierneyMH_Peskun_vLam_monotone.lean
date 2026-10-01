-- Prove2me | Theorems.Thm_TierneyMH_Peskun_vLam_monotone
-- name    : TierneyMH.Peskun.vLam_monotone
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-29T12:49:23.934418+00:00
-- url     : https://prove2.me/theorems/0412a7d0-0693-4d33-bf5c-79e1423f1dee
-- title:
--   $v_\lambda(f,P_1) \le v_\lambda(f,P_2)$ for $0 \le \lambda < 1$ when $P_1 \succeq P_2$
-- statement:
--   Let $(E,\mathcal E)$ be a measurable space in which singletons are measurable, let $\pi$ be a probability measure on $E$, let $P_1, P_2$ be Markov kernels on $E$ that are both reversible with respect to $\pi$, suppose $P_1 \succeq P_2$ (off-diagonal domination), and let $f \in L^2_0(\pi)$. Then for every $0 \le \lambda < 1$,
--
--   $$
--   v_\lambda(f, P_1) \;\le\; v_\lambda(f, P_2),
--   $$
--
--   where $v_\lambda(f,H) = \langle f, f\rangle + 2\sum_{k\ge1}\lambda^k\langle f, H^k f\rangle$ is the regularized asymptotic variance.
--
--   Letting $\lambda \uparrow 1$ turns this inequality into Theorem 4.
--
--   **Formalization Note** The series form of $v_\lambda$ replaces the paper's operator form $\langle f,(I-\lambda H)^{-1}(I+\lambda H)f\rangle$ (see the definition of $v_\lambda$). Measurability of singletons is the paper's implicit assumption that $A\setminus\{x\}$ is an event.
-- source:
--   L. Tierney, A Note on Metropolis–Hastings Kernels for General State Spaces, Ann. Appl. Probab. 8(1) (1998) 1–9, DOI 10.1214/aoap/1027961031, p. 6, proof of Theorem 4 (v_λ(f, P_2) = h_λ(1) ≥ h_λ(0) = v_λ(f, P_1))

import Mathlib
import Definitions.Def_TierneyMH_Shared_OffDiagDominates
import Definitions.Def_TierneyMH_Peskun_vLam

open TierneyMH.Shared

open MeasureTheory ProbabilityTheory

namespace TierneyMH.Peskun

/-- **Proof of Theorem 4** (Tierney 1998, p. 6), stated through the Neumann series of `vLam`.
Let `P₁ P₂` be reversible Markov kernels with invariant distribution `π`, `P₁ ⪰ P₂`, and
`f ∈ L²₀(π)`. Then for every `0 ≤ λ < 1`, `v_λ(f, P₂) ≥ v_λ(f, P₁)`. -/
theorem vLam_monotone {E : Type*} [MeasurableSpace E] [MeasurableSingletonClass E]
    (π : Measure E) [IsProbabilityMeasure π]
    (P₁ P₂ : Kernel E E) [IsMarkovKernel P₁] [IsMarkovKernel P₂]
    (hrev₁ : Kernel.IsReversible P₁ π) (hrev₂ : Kernel.IsReversible P₂ π)
    (hdom : OffDiagDominates π P₁ P₂)
    (f : E → ℝ) (hf_meas : Measurable f) (hf : MemLp f 2 π) (hf0 : ∫ x, f x ∂π = 0)
    (lam : ℝ) (hlam0 : 0 ≤ lam) (hlam1 : lam < 1) :
    vLam π P₁ f lam ≤ vLam π P₂ f lam := by sorry

end TierneyMH.Peskun
