-- Prove2me | Theorems.Thm_TailRiskSharing_VaRConv_nfold_reduction
-- name    : TailRiskSharing.VaRConv.nfold_reduction
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T18:19:50.353702+00:00
-- url     : https://prove2.me/theorems/827129b7-cbb2-4ce1-80ff-47ea37110217
-- title:
--   Proof of Theorem 1(i), p. 10 — □_{i≤n+1} VaR^{Λᵢ}_{αᵢ} = (□_{i≤n} VaR^{Λᵢ}_{αᵢ}) □ VaR^{Λ_{n+1}}_{α_{n+1}}
-- statement:
--   Let $(\Omega,\mathcal F,\mathbb P)$ be an atomless probability space, $n\ge1$, levels $\alpha_1,\dots,\alpha_{n+1}>0$ with $\sum_{i=1}^{n+1}\alpha_i<1$, and sides $\Lambda_1,\dots,\Lambda_{n+1}\in\{L,R\}$. For every random variable $X$,
--
--   $$\mathop{\square}_{i=1}^{n+1}\mathrm{VaR}^{\Lambda_i}_{\alpha_i}(X)=\Big(\mathop{\square}_{i=1}^{n}\mathrm{VaR}^{\Lambda_i}_{\alpha_i}\Big)\,\square\,\mathrm{VaR}^{\Lambda_{n+1}}_{\alpha_{n+1}}(X),$$
--
--   where the right-hand side is $\inf\{\square_{i=1}^n\mathrm{VaR}^{\Lambda_i}_{\alpha_i}(Y)+\mathrm{VaR}^{\Lambda_{n+1}}_{\alpha_{n+1}}(Z): Y,Z\in L^0,\ Y+Z=X\}$.
--
--   This is one step of the identity $\square_{i=1}^n\mathrm{VaR}^{\Lambda_i}_{\alpha_i}=\mathrm{VaR}^{\Lambda_1}_{\alpha_1}\square\cdots\square\mathrm{VaR}^{\Lambda_n}_{\alpha_n}$ that the paper takes from Lemma 2 of Liu et al. (2020); applied repeatedly, it reduces the $n$-agent problem of Theorem 1(i) to the two-agent formulas (7) and (8).
--
--   **Formalization Note** The inner inf-convolution of the first $n$ agents is valued in $[-\infty,\infty]$; since the last agent's VaR is real, the sum in the outer infimum never meets $-\infty+\infty$. The paper's left-to-right bracketing $\mathrm{VaR}^{\Lambda_1}_{\alpha_1}\square\cdots\square\mathrm{VaR}^{\Lambda_n}_{\alpha_n}$ is the iteration of this one-step identity.
-- source:
--   Liu, Mao, Wang & Wei, Inf-convolution, Optimal Allocations, and Model Uncertainty for Tail Risk Measures, SSRN 3490348 (version of January 16, 2022), p. 10, proof of Theorem 1(i), unnumbered display after 'By Lemma 2 of Liu et al. (2020)'

import Mathlib
import Definitions.Def_TailRiskSharing_VaRConv_Setting

open MeasureTheory ProbabilityTheory

namespace TailRiskSharing.VaRConv

theorem nfold_reduction {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (hP : IsAtomless P)
    (n : ℕ) (hn : 1 ≤ n) (αs : Fin (n + 1) → ℝ) (hα : ∀ i, 0 < αs i) (hsum : ∑ i, αs i < 1)
    (Λs : Fin (n + 1) → Side) (X : Ω → ℝ) (hX : X ∈ (L0 : Set (Ω → ℝ))) :
    infConv L0 (fun i => VaRS P (Λs i) (αs i)) X =
      infConv2E L0
        (infConv L0 (fun i : Fin n => VaRS P (Λs i.castSucc) (αs i.castSucc)))
        (VaRS P (Λs (Fin.last n)) (αs (Fin.last n))) X := by sorry

end TailRiskSharing.VaRConv
