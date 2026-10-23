-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P75_tensorWidthConstruction
-- name    : QAlgorithms.Papers.Independent.Information100.P75.tensorWidthConstruction
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T13:08:35.12183+00:00
-- url     : https://prove2.me/theorems/65729f1e-44e2-4241-ae54-2cf9b2720082
-- title:
--   Tensor width and the three witness constructions
-- statement:
--   For $0\le\alpha<\pi$, the relaxed-state set consists of the matrices $\Omega_n(\alpha)=\{e^{i\alpha/2}P+e^{-i\alpha/2}Q:P,Q\succeq0,\ \operatorname{Tr}(P)+\operatorname{Tr}(Q)=1\}$. Here $P,Q$ are square complex matrices of the indicated dimension; these phase-weighted sums need not be density matrices.
--
--   For a square complex matrix $X$, $W(X)$ denotes its numerical range, equivalently the values $\operatorname{Tr}(\sigma X)$ over PSD matrices $\sigma$ of trace one. Put $\Gamma_X=\{\theta\in[-\pi,\pi):\operatorname{Re}(e^{i\theta}X)\succeq0\}$, where $\operatorname{Re}Y=(Y+Y^\dagger)/2$, with Lebesgue length $|\Gamma_X|$ in radians. The ordinary width is $\operatorname{sw}(X)=\pi$ when $0\in W(X)$ and $\pi-|\Gamma_X|$ otherwise. For a complex subspace $\mathcal M$, $\operatorname{sw}^*(\mathcal M)=\inf_{X\in\mathcal M}\operatorname{sw}(X)$. The overlined width of a nonzero matrix is $\overline{\operatorname{sw}}(X)=\pi-|\Gamma_X|$.
--
--   Let $\mathcal A\subset M_n(\mathbb C)$ and $\mathcal B\subset M_m(\mathbb C)$ be complex subspaces with $n,m\ge1$. Their tensor product is the complex span of simple tensors. Put $w_A=\operatorname{sw}^*(\mathcal A)$, $w_B=\operatorname{sw}^*(\mathcal B)$ and $\alpha_A=\pi-w_A$, $\alpha_B=\pi-w_B$. Then
--
--   $$\operatorname{sw}^*(\mathcal A\otimes\mathcal B)=\min\{w_A+w_B,\pi\}.$$
--
--   For each positive-width subspace there exist PSD parts $P_A,Q_A$ with total trace one such that $\rho_A=e^{i\alpha_A/2}P_A+e^{-i\alpha_A/2}Q_A$ annihilates that subspace. At zero width set $\rho_A=I_n/n$; use the analogous convention for $\mathcal B$. Every admissible choice of these parts gives the following probe $\rho$:
--
--   1. If either width is zero, $\rho=\rho_A\otimes\rho_B$.
--   2. If both widths are positive and $w_A+w_B<\pi$, set $\theta=\alpha_A+\alpha_B-\pi$ and $c=\operatorname{Tr}(P_A)\operatorname{Tr}(P_B)+\operatorname{Tr}(Q_A)\operatorname{Tr}(Q_B)>0$. Then $\rho=c^{-1}(e^{i\theta/2}P_A\otimes P_B+e^{-i\theta/2}Q_A\otimes Q_B)$.
--   3. If both widths are positive and $w_A+w_B\ge\pi$, set $H=\rho_A\otimes\rho_B^\dagger+\rho_A^\dagger\otimes\rho_B$. Its trace is real and positive, and $\rho=H/\operatorname{Tr}H$.
--
--   When the resulting tensor width $w$ is positive, $\rho\in\Omega_{nm}(\pi-w)$ and $\operatorname{Tr}(\rho X)=0$ for every $X\in\mathcal A\otimes\mathcal B$. When $w=0$, the construction gives the conventional $I_{nm}/(nm)$. These formulas give explicit binary witness combinations.
-- source:
--   Parallel quantum channel discrimination and numerical ranges in tensor product subspaces, arXiv:2609.20781v1, PDF p. 4, Theorem 3

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P75

noncomputable section

namespace QAlgorithms.Papers.Independent.Information100.P75

open Classical

open scoped ComplexConjugate ComplexOrder Matrix

open MeasureTheory

/-- Theorem 3, PDF p.4, proof pp.8–9: saturated additivity and all three explicit
recipes, valid for every admissible choice of the input parts, whose existence is concluded.
SOURCE CORRECTION: the printed unconditional Ω-membership fails when both widths are zero:
α=π is outside Ω's domain and I/(nm) is not an annihilator for span{I}⊗span{I}.
Following p.8 and the preceding convention, this branch asserts only the conventional identity.
Membership and annihilation are asserted whenever the resulting width is positive.
(3.6) is normalized by the sum of PSD-part traces, (3.7) by its positive real trace. -/
theorem tensorWidthConstruction {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (M : Submodule ℂ (Mat ι)) (L : Submodule ℂ (Mat κ)) :
    infWidth (tensorSpace M L) = min (infWidth M + infWidth L) Real.pi ∧
    (∃ P Q, WitnessParts M P Q) ∧ (∃ R S, WitnessParts L R S) ∧
    ∀ P Q R S, WitnessParts M P Q → WitnessParts L R S →
      ValidProbe (tensorSpace M L) (combineProbe M L P Q R S) ∧
      (0 < infWidth M → 0 < infWidth L → infWidth M + infWidth L < Real.pi →
        0 < pairMass P Q R S) ∧
      (0 < infWidth M → 0 < infWidth L → Real.pi ≤ infWidth M + infWidth L →
        0 < (saturatedNumerator (probe M P Q) (probe L R S)).trace.re) := by sorry

end QAlgorithms.Papers.Independent.Information100.P75

end
