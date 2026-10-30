-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P31_lemma29_choiBasis
-- name    : QAlgorithms.Papers.Independent.Extend50.P31.lemma29_choiBasis
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T22:43:59.816865+00:00
-- url     : https://prove2.me/theorems/c34f3a5d-e7e8-40b2-b32b-475bae6e9094
-- title:
--   Lemma 29: transposed-vectorized Choi eigenbasis
-- statement:
--   Let $G$ be a finite group and $U:G\to U(n)$ an ordinary unitary irreducible representation with $n>0$. Fix a complete family of inequivalent unitary irreducibles $\varphi^\alpha$, in fixed coordinate bases, with dimensions $d_\alpha>0$ and characters $\chi_\alpha$. Assume $U\otimes\overline U\simeq\bigoplus_{\alpha\in\Theta}\varphi^\alpha$, each occurring once. Throughout, $P_\alpha=(d_\alpha/|G|)\sum_g\chi_\alpha(g^{-1})\operatorname{Ad}_U(g)$, $\widetilde P_\alpha=\operatorname{mat}(P_\alpha)$, and $J(\Phi)=\sum_{ij}E_{ij}\otimes\Phi(E_{ij})$ is unnormalized. Fine projectors use the diagonal matrix coefficient $\varphi^\alpha(g^{-1})_{ii}$ in place of the character. Whenever vectors $V_i^\beta$ occur, choose one pivot $(s,t)$ per fine sector with $p=(\widetilde P_{\beta i})_{st,st}>0$ and set $V_i^\beta=P_{\beta i}(E_{st})/\sqrt p$ and $v_i^\beta=\operatorname{vec}((V_i^\beta)^T)$. Write $\mu_i(\alpha,\beta)=(d_\alpha/|G|)\sum_g\chi_\alpha(g^{-1})|\operatorname{Tr}(V_i^\beta U(g)^\dagger)|^2$ and $M_{(\beta,i),\alpha}=\mu_i(\alpha,\beta)$ when these spectral coordinates occur.
--
--   From one selected pivot per fine sector form $v_i^\beta=\operatorname{vec}((V_i^\beta)^T)$, with no coefficient conjugation. These vectors form a complete orthonormal basis of $\mathbb C^{n^2}$:
--
--   $$
--   \langle v_i^\alpha,v_j^\beta\rangle=\delta_{\alpha\beta}\delta_{ij},\qquad\operatorname{span}\{v_i^\beta\}=\mathbb C^{n^2}.
--   $$
--
--   This describes the transposed-vectorized Choi eigenbasis in the fixed source conventions.
-- source:
--   Structure of irreducibly covariant quantum channels for finite groups, arXiv:1610.05657v2, PDF p. 15, Lemma 29: transposed-vectorized Choi eigenbasis

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

/-- PDF p.15, Lemma 29 Eq.(75), transpose without complex conjugation. -/
theorem lemma29_choiBasis (D : Data G A n) (P : Pivots D) :
    (∀ r s, (∑ p, conj (choiVector D P r p) * choiVector D P s p) =
      if r = s then 1 else 0) ∧
    Submodule.span ℂ (Set.range (choiVector D P)) = ⊤ := by sorry

end QAlgorithms.Papers.Independent.Extend50.P31

end
