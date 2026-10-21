-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P27_optimal_unitary_cloner
-- name    : QAlgorithms.Papers.Independent.Claimed50.P27.optimal_unitary_cloner
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T10:15:28.225982+00:00
-- url     : https://prove2.me/theorems/52aeb8f5-40be-4d85-86fa-9ea3900ff8e1
-- title:
--   Optimal universal one-to-two unitary cloning, with attaining channels
-- statement:
--   Let $d\ge2$ be an integer. Each external input and output has two $d$-dimensional factors, ordered $B,E$, and the unknown unitary $U$ is used exactly once. All processing is deterministic and independent of $U$. A feasible network has an unnormalized Choi operator $R\succeq0$ obeying $\operatorname{Tr}_3R=I_2\otimes R_0$ and $\operatorname{Tr}_1R_0=I_0$. Its fidelity is the probability-Haar average of $d^{-4}\operatorname{Tr}[J(C_U)J(U^{\otimes2})]$, with input-first Choi order and the two target copies permuted accordingly. Then
--
--   $$F(R)\le F_{\mathrm{clon}}:=\frac{d+\sqrt{d^2-1}}{d^3}.$$
--
--   Write $P_\pm=(I\pm S)/2$ for the symmetric and antisymmetric projectors, $S$ for swap, and $d_\pm=d(d\pm1)/2$. In an orthonormal two-dimensional memory basis $\{|+\rangle,|-\rangle\}$ define
--
--   $$A(\rho)=\sum_{i,j=\pm}\operatorname{Tr}_E(P_i\rho P_j)\otimes|i\rangle\langle j|,\qquad B(\sigma)=\sum_{i,j=\pm}\frac d{\sqrt{d_i d_j}}P_i[\langle i|\sigma|j\rangle\otimes I]P_j.$$
--
--   Both maps are CPTP, their one-use circuit has an admissible Choi operator, and its resulting channel is exactly
--
--   $$C_U(\rho)=B\circ(\mathcal U\otimes\mathrm{id}_M)\circ A(\rho)=\sum_{i,j=\pm}\frac d{\sqrt{d_i d_j}}P_i[U\operatorname{Tr}_E(P_i\rho P_j)U^\dagger\otimes I]P_j.$$
--
--   Here $\mathcal U(X)=UXU^\dagger$. Its pointwise fidelity equals $F_{\mathrm{clon}}$ for every $U$, and its Haar-average fidelity attains the bound. Thus the statement specifies both optimality and a physical attaining network.
-- source:
--   Optimal cloning of unitary transformations, arXiv:0804.0129v2, PDF p. 3, Theorem 1; Eqs. (8)–(10)

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P27

noncomputable section

open MeasureTheory QAlgorithms

open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.Elementwise

namespace QAlgorithms.Papers.Independent.Claimed50.P27

attribute [local instance] Classical.decEq Classical.propDecidable

/-- PDF p.3, Theorem 1, Eqs.(8)–(10): universal upper bound, physicality and attainment
by the specified channels, including the exact resulting channel formula.
The two-sector implementation requires d>=2. -/
theorem optimal_unitary_cloner (d : ℕ) (hd : 2 ≤ d) :
    (∀ R : Matrix (CombReg d) (CombReg d) ℂ, CloningAdmissible R →
      combScore R ≤ cloningValue d) ∧
    IsChannel (optimalPre d) ∧ IsChannel (optimalPost d) ∧
    (∀ U : (Matrix.unitaryGroup (Fin d) ℂ), optimalFamily d U = optimalFormula d U) ∧
    (∃ R : Matrix (CombReg d) (CombReg d) ℂ,
      CloningAdmissible R ∧
      (∀ U : (Matrix.unitaryGroup (Fin d) ℂ), insertedChoi R U = channelChoi (optimalFamily d U)) ∧
      combScore R = cloningValue d) ∧
    (∀ U : (Matrix.unitaryGroup (Fin d) ℂ), IsChannel (optimalFamily d U) ∧
      pointScore (channelChoi (optimalFamily d U)) U = cloningValue d) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P27

end
