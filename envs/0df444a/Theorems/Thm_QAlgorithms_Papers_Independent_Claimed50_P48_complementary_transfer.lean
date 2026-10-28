-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P48_complementary_transfer
-- name    : QAlgorithms.Papers.Independent.Claimed50.P48.complementary_transfer
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T11:37:25.558793+00:00
-- url     : https://prove2.me/theorems/439aa687-2455-4ff9-a051-d7a804e5489d
-- title:
--   Theorem 1: complementary transfer of multiplicativity, additivity and superadditivity
-- statement:
--   Let $\Phi_i$ and $\widetilde\Phi_i$ be complementary finite-dimensional CP maps, arising from the two partial traces of the same linear dilation for each $i=1,2$. Input spaces are nonzero. For $1\le p\le\infty$, write $\nu_p$ for the maximum output Schatten norm. For channels, write $\check H$ for minimum output entropy in nats and $\widehat H$ for its pure-ensemble convex roof. Each of the following implications holds independently:
--
--   $$
--   \begin{aligned}
--   \nu_p(\Phi_1\otimes\Phi_2)=\nu_p(\Phi_1)\nu_p(\Phi_2)&\Longrightarrow
--   \nu_p(\widetilde\Phi_1\otimes\widetilde\Phi_2)=\nu_p(\widetilde\Phi_1)\nu_p(\widetilde\Phi_2),\\
--   \check H(\Phi_1\otimes\Phi_2)=\check H(\Phi_1)+\check H(\Phi_2)&\Longrightarrow
--   \check H(\widetilde\Phi_1\otimes\widetilde\Phi_2)=\check H(\widetilde\Phi_1)+\check H(\widetilde\Phi_2),\\
--   \widehat H_{\Phi_1\otimes\Phi_2}(\rho_{12})\ge\widehat H_{\Phi_1}(\rho_1)+\widehat H_{\Phi_2}(\rho_2)&\Longrightarrow
--   \widehat H_{\widetilde\Phi_1\otimes\widetilde\Phi_2}(\rho_{12})\ge\widehat H_{\widetilde\Phi_1}(\rho_1)+\widehat H_{\widetilde\Phi_2}(\rho_2).
--   \end{aligned}
--   $$
--
--   The last two implications require channels. Here $\rho_{12}$ is any joint density, and $\rho_1,\rho_2$ are its partial traces; the last implication holds for the same density, and hence also as an all-states property. If any one of the three properties holds for a fixed $\Phi_1$ with every CP partner (every channel partner for entropy), the corresponding property holds for $\widetilde\Phi_1$ with every such partner. These are conditional transfer principles, without assuming any additivity conjecture.
-- source:
--   On complementary channels and the additivity problem, arXiv:quant-ph/0509101v3, PDF p. 3, Theorem 1: complementary transfer of multiplicativity, additivity and superadditivity

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P48

noncomputable section

namespace QAlgorithms.Papers.Independent.Claimed50.P48

open scoped BigOperators Matrix Kronecker ComplexConjugate ComplexOrder ENNReal

open QAlgorithms.Papers.Independent.Information100.P67 (receiverChannel complementaryChannel environmentSwap)

open QAlgorithms.Papers.Independent.Information100.P03 (PureEnsemble convexRoof)

open QAlgorithms.Papers.Independent.Information100.P50 (schattenNorm)

open QAlgorithms.Papers.Independent.Information100.P60 (wernerHolevo)

open QAlgorithms.Papers.Independent.Information100.P56 (entropy)

attribute [local instance] Classical.propDecidable Classical.decEq

variable {A B C D A2 B2 C2 K : Type*}

variable [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

variable [Fintype C] [DecidableEq C] [Fintype D] [DecidableEq D]

variable [Fintype A2] [DecidableEq A2] [Fintype B2] [DecidableEq B2]

variable [Fintype C2] [DecidableEq C2] [Fintype K] [DecidableEq K]

/-- Theorem 1, PDF pp.3–4: all three implications, pointwise AND all-input
superadditivity, and all three arbitrary-partner clauses. -/
theorem complementary_transfer [Nonempty A] [Nonempty A2]
    (Phi : Superop A B) (PhiC : Superop A C) (Psi : Superop A2 B2) (PsiC : Superop A2 C2)
    (hPhi : CPComplementary Phi PhiC) (hPsi : CPComplementary Psi PsiC)
    (p : ℝ≥0∞) (hp : ValidExponent p) :
    (Multiplicative p Phi Psi → Multiplicative p PhiC PsiC) ∧
    (IsChannel Phi → IsChannel Psi →
      (Additive Phi Psi → Additive PhiC PsiC) ∧
      (∀ rho, IsDensityMatrix rho → SuperadditiveAt Phi Psi rho → SuperadditiveAt PhiC PsiC rho) ∧
      (Superadditive Phi Psi → Superadditive PhiC PsiC)) ∧
    (UniversalMultiplicative p Phi → UniversalMultiplicative p PhiC) ∧
    (IsChannel Phi → (UniversalAdditive Phi → UniversalAdditive PhiC) ∧
      (UniversalSuperadditive Phi → UniversalSuperadditive PhiC)) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P48

end
