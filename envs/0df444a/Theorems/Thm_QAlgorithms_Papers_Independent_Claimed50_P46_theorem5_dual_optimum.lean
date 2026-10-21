-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P46_theorem5_dual_optimum
-- name    : QAlgorithms.Papers.Independent.Claimed50.P46.theorem5_dual_optimum
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T11:28:35.100993+00:00
-- url     : https://prove2.me/theorems/6cc59b44-9beb-4dd3-9041-28f2d70b942e
-- title:
--   Theorem 5: dual correct-testing optimum (90)–(92)
-- statement:
--   Work in the classical or quantum testing model on finite or countable alphabets or arbitrary complex Hilbert spaces, respectively, with the normalization $0<\rho_n[I]\le\infty$, $\sigma_n[I]=1$. Classical weights are pointwise finite and quantum weights are bounded positive operators. All effects are permitted as tests. Define $\alpha_n[T_n]=\rho_n[I-T_n]$ and $\beta_n[T_n]=\sigma_n[T_n]$. Write $\eta_L,\eta_U$ for the liminf and limsup of $-\log\alpha_n/n$, and $\zeta_L^c,\zeta_U^c$ for the liminf and limsup of $-\log\sigma_n[I-T_n]/n$. These are extended real values with natural logarithms. Choose any likelihood family $S_n(a)$ allowed by (6), including any effect on the zero subspace. An exponent evaluated at $a$ refers to this family; tests in operational optimizations range independently over all test sequences.
--
--   For every real $r$, define $B_e^{**}(r)=\sup\{\eta_L[T]:\zeta_U^c[T]\le r\}$. Then
--   $$
--   B_e^{**}(r)=\sup\{r'\in\mathbb R:B_e^*(r')\le r\}=r-a_0^{**},
--   $$
--   where
--   $$
--   a_0^{**}=\inf\{a\in\mathbb R:\zeta_U^c(a)\le r\}
--   =\sup\{a\in\mathbb R:\zeta_U^c(a)>r\}.
--   $$
--
--   The dual formula keeps both operational representations and both cutoff sets.
-- source:
--   An Information-Spectrum Approach to Classical and Quantum Hypothesis Testing for Simple Hypotheses, arXiv:quant-ph/0206185v2, PDF p. 17, Theorem 5: dual correct-testing optimum (90)–(92)

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P46

noncomputable section

open Filter

open scoped BigOperators ENNReal NNReal

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

open QAlgorithms.Papers.Independent.Dependency50.P13 (IsPositive State relativeEntropy)

universe u

namespace QAlgorithms.Papers.Independent.Claimed50.P46

/-- Theorem 5, PDF p.17, (90)–(92): both dual representations and both cutoff sets. -/
theorem theorem5_dual_optimum (P : ℕ → SimpleHypothesisSystem.{u}) (hP : SwitchedNormalization P)
    (S : LikelihoodFamily P) (r : ℝ) :
    let c := sInf {z | ∃ a : ℝ, zetaUc (S.tests a) ≤ (r : EReal) ∧ z = (a : EReal)}
    dualTradeoff P r = sSup {z | ∃ t : ℝ, correctTradeoff P true false t ≤ (r : EReal) ∧
      z = (t : EReal)} ∧
    dualTradeoff P r = (r : EReal) - c ∧
    c = sSup {z | ∃ a : ℝ, (r : EReal) < zetaUc (S.tests a) ∧ z = (a : EReal)} := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P46

end
