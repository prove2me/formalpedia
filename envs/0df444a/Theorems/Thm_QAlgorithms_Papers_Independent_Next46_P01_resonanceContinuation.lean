-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P01_resonanceContinuation
-- name    : QAlgorithms.Papers.Independent.Next46.P01.resonanceContinuation
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T18:33:42.721091+00:00
-- url     : https://prove2.me/theorems/2d9112f6-a7d9-4dfc-b939-6de6f7e832a0
-- title:
--   Polynomial exponential asymptotics give a sole resolvent pole
-- statement:
--   Let $U_t=e^{-itL}$, $\mathcal H$, $M,m>0$, and $\varphi,\psi$ be as in Proposition 4.1. Let $r\in\mathbb C$, $N\ge1$, $\gamma>\max(0,-\operatorname{Im}r)$, and let $p$ be a nonzero complex polynomial of exact degree $N-1$. Suppose that the actual remainder satisfies
--   $$
--   R(t)=\langle\varphi,U_t\psi\rangle-e^{-itr}p(t)=O(e^{-\gamma t})\qquad(t\to+\infty).
--   $$
--   Then the scalar coefficient $\langle\varphi,(z-L)^{-1}\psi\rangle$, initially on $\operatorname{Im}z>m$, admits a meromorphic continuation $f$ to $\operatorname{Im}z>-\gamma$ whose sole singularity is a pole of exact order $N$ at $r$. There is a cutoff $A>0$ such that for every $0<\mu<\gamma$,
--   $$
--   \sup_{y>-\mu}\int_{|x|>A}|f(x+iy)|^2\,dx<\infty.
--   $$
--   If $R$ is twice differentiable and $R'(t),R''(t)=O(e^{-\gamma t})$, then the same cutoff also satisfies
--   $$
--   \sup_{y>-\mu}\int_{|x|>A}|f'(x+iy)|\,dx<\infty\qquad(0<\mu<\gamma).
--   $$
--   This converse preserves both the exact pole multiplicity and the distinct regularity requirement for the derivative tail. The original operator group is not assumed to be twice differentiable.
-- source:
--   Entropic Fluctuations in Statistical Mechanics II. Quantum Dynamical Systems, arXiv:2409.15485v2, PDF p. 32, proposition-4.2

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P01

noncomputable section

open Filter MeasureTheory Set

open scoped BigOperators ComplexConjugate ComplexOrder Matrix.Norms.L2Operator Topology ENNReal

namespace QAlgorithms.Papers.Independent.Next46.P01

section Resonance

variable (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {H}

/-- Proposition 4.2: arXiv:2409.15485v2, PDF p.32.
The cutoff is chosen before mu, the pole has exact order N, and only the
optional j=1 conclusion requires differentiability of the actual remainder. -/
theorem resonanceContinuation (U : StrongOperatorGroup H) (M m : ℝ)
    (hgrowth : HasGroupGrowth U M m) (phi psi : H)
    (r : ℂ) (gamma : ℝ) (hgamma : max 0 (-r.im) < gamma)
    (N : ℕ) (hN : 1 ≤ N) (p : Polynomial ℂ) (hp : p ≠ 0)
    (hdegree : p.natDegree = N - 1)
    (hdecay : Asymptotics.IsBigO atTop (resonanceRemainder U phi psi r p)
      (fun t : ℝ => Real.exp (-gamma * t))) :
    ∃ f : ℂ → ℂ,
      (∀ z : ℂ, m < z.im → f z = groupResolventCoefficient U phi psi z) ∧
      HasSolePole f gamma r N ∧
      ∃ R : ℝ, 0 < R ∧ ∀ mu : ℝ, 0 < mu → mu < gamma →
        HasUniformResolventTail f mu R 0 ∧
        (HasTwoDecayingDerivatives (resonanceRemainder U phi psi r p) gamma →
          HasUniformResolventTail f mu R 1) := by sorry

end Resonance

end QAlgorithms.Papers.Independent.Next46.P01

end
