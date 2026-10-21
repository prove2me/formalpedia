-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P01_resonanceAsymptotic
-- name    : QAlgorithms.Papers.Independent.Next46.P01.resonanceAsymptotic
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T18:33:13.990785+00:00
-- url     : https://prove2.me/theorems/e817a1a8-b46f-439a-a6a3-67e98a72d73f
-- title:
--   A sole resolvent pole gives polynomial exponential asymptotics
-- statement:
--   Let $\mathcal H$ be a complex Hilbert space and $U_t=e^{-itL}$ a strongly continuous group of bounded operators with $\|U_t\|\le M e^{m|t|}$ for fixed $M,m>0$. Fix $\varphi,\psi\in\mathcal H$. On $\operatorname{Im}z>m$, the scalar resolvent coefficient is
--   $$
--   f(z)=\langle\varphi,(z-L)^{-1}\psi\rangle
--   =-i\int_0^\infty e^{izt}\langle\varphi,U_t\psi\rangle\,dt.
--   $$
--   Suppose that $f$ has a meromorphic continuation to $\operatorname{Im}z>-\mu$, with $\mu>0$, whose only singularity is a pole of exact order $N\ge1$ at $r$. Suppose that for one $R>0$ and $j=0,1$,
--   $$
--   \sup_{y>-\mu}\int_{|x|>R}|\partial_z^j f(x+iy)|^{2-j}\,dx<\infty.
--   $$
--   Then there is a nonzero complex polynomial $p$ of exact degree $N-1$, with $p(0)=\operatorname{Res}_{z=r}f$, such that, for every $\max(-\operatorname{Im}r,0)<\gamma<\mu$,
--   $$
--   \langle\varphi,U_t\psi\rangle=e^{-itr}p(t)+O(e^{-\gamma t})\qquad(t\to+\infty).
--   $$
--   For $N=1$ the polynomial is the constant residue. The remainder constant may depend on the chosen $\gamma$ and the fixed data. No self-adjointness of $L$ is assumed.
--
--   **Formalization Note** The scalar coefficient is defined by its displayed, convergent Laplace integral on the initial half-plane. Exact pole order is encoded by the nonvanishing holomorphic numerator after multiplication by $(z-r)^N$. Residue is the actual positively oriented circle integral inside the continued half-plane.
-- source:
--   Entropic Fluctuations in Statistical Mechanics II. Quantum Dynamical Systems, arXiv:2409.15485v2, PDF p. 31, proposition-4.1

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P01

noncomputable section

open Filter MeasureTheory Set

open scoped BigOperators ComplexConjugate ComplexOrder Matrix.Norms.L2Operator Topology ENNReal

namespace QAlgorithms.Papers.Independent.Next46.P01

section Resonance

variable (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {H}

/-- Proposition 4.1: arXiv:2409.15485v2, PDF pp.31--32.
The continuation agrees with the source's Laplace resolvent coefficient only
on its initial half-plane. The polynomial has exact degree N-1 and the source
residue as constant coefficient; each decay constant may depend on gamma. -/
theorem resonanceAsymptotic (U : StrongOperatorGroup H) (M m : ℝ)
    (hgrowth : HasGroupGrowth U M m) (phi psi : H)
    (f : ℂ → ℂ) (mu : ℝ) (hmu : 0 < mu) (r : ℂ) (N : ℕ)
    (hcontinuation : ∀ z : ℂ, m < z.im → f z = groupResolventCoefficient U phi psi z)
    (hpole : HasSolePole f mu r N)
    (htails : ∃ R : ℝ, 0 < R ∧
      HasUniformResolventTail f mu R 0 ∧ HasUniformResolventTail f mu R 1) :
    ∃ p : Polynomial ℂ, p ≠ 0 ∧ p.natDegree = N - 1 ∧
      p.eval 0 = halfPlaneResidue f mu r ∧
      (N = 1 → p = Polynomial.C (halfPlaneResidue f mu r)) ∧
      ∀ gamma : ℝ, max (-r.im) 0 < gamma → gamma < mu →
        Asymptotics.IsBigO atTop (resonanceRemainder U phi psi r p)
          (fun t : ℝ => Real.exp (-gamma * t)) := by sorry

end Resonance

end QAlgorithms.Papers.Independent.Next46.P01

end
