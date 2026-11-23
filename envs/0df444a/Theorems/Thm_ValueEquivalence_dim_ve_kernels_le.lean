-- Prove2me | Theorems.Thm_ValueEquivalence_dim_ve_kernels_le
-- name    : ValueEquivalence.dim_ve_kernels_le
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-23T17:52:24.890561+00:00
-- url     : https://prove2.me/theorems/0e782089-776f-40b2-8a8b-eb6c2a90f9af
-- title:
--   Proposition 2 (as proved): the dimension of the value-equivalent transition matrices
-- statement:
--   Let $S,A$ be finite, $0<\gamma<1$, and let $m^*=(r^*,p^*)$ be the true model with known reward $r^*$. Let $\pi_1,\dots,\pi_m$ be policies such that at every state $s$ the vectors $\pi_1(\cdot\mid s),\dots,\pi_m(\cdot\mid s)\in\mathbb R^{A}$ are linearly independent, and let $v_1,\dots,v_k\in\mathbb R^{S}$ be linearly independent. Let $\Pi=\{\pi_i\}$, $\mathcal V=\{v_j\}$, and let $\mathbb P(\Pi,\mathcal V)$ be the set of transition kernels $\tilde p$ for which $(r^*,\tilde p)$ is value equivalent to $m^*$ with respect to $\Pi$ and $\mathcal V$, viewed as a subset of $\mathbb R^{S\times A\times S}$. Then
--
--   $$\dim\big[\mathbb P(\Pi,\mathcal V)\big]\le|S|\big(|S||A|-mk\big).$$
--
--   Policies and functions thus reduce the dimension of the value-equivalent transition models multiplicatively.
--
--   **Formalization Note** The paper assumes only that the policies are pointwise linearly independent ($\pi_i\notin p\text{-span}(\Pi\setminus\{\pi_i\})$). Its proof uses $\operatorname{rank}(\boldsymbol\Pi)=m|S|$ for the stacked policy matrix, which holds exactly when the policies are linearly independent at every state; this is the hypothesis stated here, and for $S\ne\emptyset$ it implies pointwise linear independence (for $S=\emptyset$ both sides of the inequality are $0$). Under the paper's weaker hypothesis the bound fails: for $|S|=|A|=2$, $\pi_1=((1,0),(1,0))$, $\pi_2=((1,0),(0,1))$ and $\mathcal V$ a basis, the bound is $0$ while $\mathbb P(\Pi,\mathcal V)$ has dimension $1$ for $p^*$ with full support. The paper allows $\gamma=0$, for which every kernel is value equivalent; the proof's identity $\mathbb P(\Pi,\mathcal V)=\{\tilde{\boldsymbol P}:\boldsymbol\Pi(\tilde{\boldsymbol P}-\boldsymbol P)\boldsymbol V=0\}$ needs $\gamma>0$. The inequality is stated in the integers.
-- source:
--   Grimm, Barreto, Singh and Silver, The Value Equivalence Principle for Model-Based Reinforcement Learning, arXiv:2011.03506v1 (2020), Section 3.2, Proposition 2, p. 5; proof in Appendix A.1.1, p. 15

import Mathlib
import Definitions.Def_ValueEquivalence_Basic

open Filter Topology

namespace ValueEquivalence

theorem dim_ve_kernels_le {S A : Type*} [Fintype S] [Fintype A] {m k : ℕ}
    (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1) (mstar : Model S A)
    (pol : Fin m → S → A → ℝ) (hpol : ∀ i, pol i ∈ policies)
    (hind : ∀ s, LinearIndependent ℝ (fun i => pol i s))
    (vs : Fin k → S → ℝ) (hvs : LinearIndependent ℝ vs) :
    (setDim (veKernels γ mstar Set.univ (Set.range pol) (Set.range vs)) : ℤ) ≤
      (Fintype.card S : ℤ) * ((Fintype.card S : ℤ) * Fintype.card A - (m : ℤ) * k) := by sorry

end ValueEquivalence
