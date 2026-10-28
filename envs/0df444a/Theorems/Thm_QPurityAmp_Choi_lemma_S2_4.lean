-- Prove2me | Theorems.Thm_QPurityAmp_Choi_lemma_S2_4
-- name    : QPurityAmp.Choi.lemma_S2_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:31:32.631077+00:00
-- url     : https://prove2.me/theorems/ca37d27e-0097-4131-a080-9127c3e22bc4
-- title:
--   Lemma S2.4, p. 20 — cost matrices with P(C₁) = A·P(C₂), A > 0, have the same optimal Choi matrices
-- statement:
--   Let $d\ge 1$, let $\mathrm{in}$ be a finite register, and consider the SDP over operators $T$ on $\mathbb C^d\otimes\mathrm{in}$
--   $$\text{maximize }\ \mathrm{Re}\,\mathrm{tr}(KT)\quad\text{subject to}\quad T\succeq 0,\ \ \mathrm{tr}_{\mathrm{out}}T=\mathbb I_{\mathrm{in}} .$$
--   If two cost matrices $C_1,C_2$ satisfy
--   $$P(C_1)=A\,P(C_2)$$
--   for a real number $A>0$, where $P=\mathrm{Id}-\frac{\mathbb I}{d}\otimes\mathrm{tr}_{\mathrm{out}}$ is the projection of Lemma S2.3, then a matrix $T_0$ is an optimal solution of the SDP with cost $C_1$ if and only if it is an optimal solution of the SDP with cost $C_2$.
--
--   This is what allows the proof of Theorem II.1 to replace the Haar cost matrix $C$ by the more symmetric $C'$.
--
--   **Formalization Note** The lemma writes the objective as $\mathrm{tr}(CT)$, without the transpose of SDP (1); it is stated here as printed. Since $P$ commutes with transposition, it applies to the SDP (1) with $C_1^\top, C_2^\top$. The constraint is $\mathrm{tr}_{\mathrm{out}}T=\mathbb I$ as in Eqs. (1) and (S16) (Fig. S7 normalizes by $d^{[\varsigma]}$ instead; the lemma holds for either). "Yield the same optimal solution" is read as: the two SDPs have the same set of optimal solutions. The real part is taken because a general complex cost gives a complex trace.
-- source:
--   Li, Fu, Isogawa, Silva and Chuang, Optimal Quantum Purity Amplification, arXiv:2409.18167v4, p. 20, Lemma S2.4 and its proof, Eq. (S24)

import Mathlib
import Definitions.Def_QPurityAmp_Choi_OptimalChoi
noncomputable section

namespace QPurityAmp.Choi

open scoped Matrix

/-- Lemma S2.4, p. 20 (Equivalence of cost matrices): if P(C₁) = A·P(C₂) for a positive
scalar A, the SDPs "maximize tr(C T) subject to T ⪰ 0, tr_out T = I" with cost C₁ and with
cost C₂ have the same optimal solutions. -/
theorem lemma_S2_4 {d : ℕ} [NeZero d] {ι : Type} [Fintype ι] [DecidableEq ι]
    (C₁ C₂ : Matrix (Fin d × ι) (Fin d × ι) ℂ) (A : ℝ) (hA : 0 < A)
    (hP : projP C₁ = (A : ℂ) • projP C₂) (T₀ : Matrix (Fin d × ι) (Fin d × ι) ℂ) :
    IsOptimal C₁ T₀ ↔ IsOptimal C₂ T₀ := by sorry

end QPurityAmp.Choi
