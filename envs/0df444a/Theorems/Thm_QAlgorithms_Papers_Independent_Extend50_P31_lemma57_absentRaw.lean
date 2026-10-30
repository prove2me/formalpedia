-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P31_lemma57_absentRaw
-- name    : QAlgorithms.Papers.Independent.Extend50.P31.lemma57_absentRaw
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T23:03:10.710988+00:00
-- url     : https://prove2.me/theorems/29bbe8a9-68fc-4172-8883-a4989569402f
-- title:
--   Lemma 57: raw eigenmatrices vanish for absent irreps
-- statement:
--   Let $G$ be a finite group and $U:G\to U(n)$ an ordinary unitary irreducible representation with $n>0$. Fix a complete family of inequivalent unitary irreducibles $\varphi^\alpha$, in fixed coordinate bases, with dimensions $d_\alpha>0$ and characters $\chi_\alpha$. Assume $U\otimes\overline U\simeq\bigoplus_{\alpha\in\Theta}\varphi^\alpha$, each occurring once. Throughout, $P_\alpha=(d_\alpha/|G|)\sum_g\chi_\alpha(g^{-1})\operatorname{Ad}_U(g)$, $\widetilde P_\alpha=\operatorname{mat}(P_\alpha)$, and $J(\Phi)=\sum_{ij}E_{ij}\otimes\Phi(E_{ij})$ is unnormalized. Fine projectors use the diagonal matrix coefficient $\varphi^\alpha(g^{-1})_{ii}$ in place of the character. Whenever vectors $V_i^\beta$ occur, choose one pivot $(s,t)$ per fine sector with $p=(\widetilde P_{\beta i})_{st,st}>0$ and set $V_i^\beta=P_{\beta i}(E_{st})/\sqrt p$ and $v_i^\beta=\operatorname{vec}((V_i^\beta)^T)$. Write $\mu_i(\alpha,\beta)=(d_\alpha/|G|)\sum_g\chi_\alpha(g^{-1})|\operatorname{Tr}(V_i^\beta U(g)^\dagger)|^2$ and $M_{(\beta,i),\alpha}=\mu_i(\alpha,\beta)$ when these spectral coordinates occur.
--
--   For every absent irreducible label $\gamma\notin\Theta$, every $1\le i\le d_\gamma$ and every pivot $(s,t)$, the raw matrix vanishes:
--
--   $$
--   W_{\gamma i}(s,t)=P_{\gamma i}(E_{st})=\frac{d_\gamma}{|G|}\sum_g\varphi^\gamma(g^{-1})_{ii}U(g)E_{st}U(g)^\dagger=0.
--   $$
--
--   This describes the raw eigenmatrices vanish for absent irreps in the fixed source conventions.
-- source:
--   Structure of irreducibly covariant quantum channels for finite groups, arXiv:1610.05657v2, PDF p. 31, Lemma 57: raw eigenmatrices vanish for absent irreps

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P31

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Extend50.P31

open QAlgorithms.Papers.Independent.Information100.P44 (Mat matrixUnit)

open QAlgorithms.Papers.Independent.Frontier18.P17 (hs)

open QAlgorithms.Papers.Independent.Bridge50.P37 (hsAdjoint)

open QAlgorithms.Papers.Independent.Information100.P34 (choi)

open QAlgorithms.Papers.Independent.Dependency50.P26 (TracePreserving)

open QAlgorithms.Papers.Independent.Dependency50.P16 (sandwich)

open QAlgorithms.Papers.Independent.Information100.P75 (phase)

variable {G A : Type*} [Group G] [Fintype G] [Fintype A] [DecidableEq A] {n : ℕ}

/-- PDF p.31, Lemma 57 Eq.(156): raw W, so absent labels and zero pivots are meaningful. -/
theorem lemma57_absentRaw (D : Data G A n) (a : A) (ha : a ∉ D.theta)
    (i : Fin (D.F.dim a)) (p : Fin n × Fin n) :
    rawMatrix D.U D.F a i p = 0 := by sorry

end QAlgorithms.Papers.Independent.Extend50.P31

end
