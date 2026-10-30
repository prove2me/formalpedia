-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P31_proposition26_choi
-- name    : QAlgorithms.Papers.Independent.Extend50.P31.proposition26_choi
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T22:42:26.595958+00:00
-- url     : https://prove2.me/theorems/dbbff584-4cde-459b-9fcd-a3088f4b5b28
-- title:
--   Proposition 26: explicit Choi image of a trace-preserving ICLM
-- statement:
--   Let $G$ be a finite group and $U:G\to U(n)$ an ordinary unitary irreducible representation with $n>0$. Fix a complete family of inequivalent unitary irreducibles $\varphi^\alpha$, in fixed coordinate bases, with dimensions $d_\alpha>0$ and characters $\chi_\alpha$. Assume $U\otimes\overline U\simeq\bigoplus_{\alpha\in\Theta}\varphi^\alpha$, each occurring once. Throughout, $P_\alpha=(d_\alpha/|G|)\sum_g\chi_\alpha(g^{-1})\operatorname{Ad}_U(g)$, $\widetilde P_\alpha=\operatorname{mat}(P_\alpha)$, and $J(\Phi)=\sum_{ij}E_{ij}\otimes\Phi(E_{ij})$ is unnormalized. Fine projectors use the diagonal matrix coefficient $\varphi^\alpha(g^{-1})_{ii}$ in place of the character. Whenever vectors $V_i^\beta$ occur, choose one pivot $(s,t)$ per fine sector with $p=(\widetilde P_{\beta i})_{st,st}>0$ and set $V_i^\beta=P_{\beta i}(E_{st})/\sqrt p$ and $v_i^\beta=\operatorname{vec}((V_i^\beta)^T)$. Write $\mu_i(\alpha,\beta)=(d_\alpha/|G|)\sum_g\chi_\alpha(g^{-1})|\operatorname{Tr}(V_i^\beta U(g)^\dagger)|^2$ and $M_{(\beta,i),\alpha}=\mu_i(\alpha,\beta)$ when these spectral coordinates occur.
--
--   Let $\Phi_l=\sum_\Theta l_\alpha P_\alpha$ with $l_{\mathrm{id}}=1$. Its unnormalized input-first Choi matrix, with $E_{ij}$ the matrix units, is
--
--   $$
--   J(\Phi_l)=\frac{I_n\otimes I_n}{n}+\frac1{|G|}\sum_{i,j} E_{ij}\otimes\sum_{g\in G}\left(\sum_{\substack{\alpha\in\Theta\\\alpha\ne\mathrm{id}}}l_\alpha d_\alpha\chi_\alpha(g^{-1})\right)U(g)E_{ij}U(g)^\dagger.
--   $$
--
--   This describes the explicit Choi image of a trace-preserving ICLM in the fixed source conventions.
-- source:
--   Structure of irreducibly covariant quantum channels for finite groups, arXiv:1610.05657v2, PDF p. 14, Proposition 26: explicit Choi image of a trace-preserving ICLM

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

/-- PDF p.14, Proposition 26 Eq.(72); unnormalized J has I tensor I/n. -/
theorem proposition26_choi (D : Data G A n) (l : OccurringIrrep D → ℂ)
    (hl : trivialCoefficient D l = 1) :
    choi (spectralMap D l) = (n : ℂ)⁻¹ • (1 : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ) +
      (Fintype.card G : ℂ)⁻¹ • ∑ i : Fin n, ∑ j : Fin n,
        Matrix.kronecker (matrixUnit i j)
          (∑ g : G, (∑ a : OccurringIrrep D,
            if a.val = D.F.trivial then 0 else
              l a * (D.F.dim a.val : ℂ) * character (D.F.irrep a.val) g⁻¹) •
            (D.U.rho g * matrixUnit i j * (D.U.rho g)ᴴ)) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P31

end
