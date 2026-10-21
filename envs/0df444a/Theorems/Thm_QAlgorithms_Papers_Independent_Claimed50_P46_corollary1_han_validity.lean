-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P46_corollary1_han_validity
-- name    : QAlgorithms.Papers.Independent.Claimed50.P46.corollary1_han_validity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T11:26:21.155743+00:00
-- url     : https://prove2.me/theorems/d669300d-e571-40d4-95d5-45550ee0b97c
-- title:
--   Corollary 1: validity conditions for Han's formula (78)–(81)
-- statement:
--   Work in the classical or quantum testing model on finite or countable alphabets or arbitrary complex Hilbert spaces, respectively, with the normalization $0<\rho_n[I]\le\infty$, $\sigma_n[I]=1$. Classical weights are pointwise finite and quantum weights are bounded positive operators. All effects are permitted as tests. Define $\alpha_n[T_n]=\rho_n[I-T_n]$ and $\beta_n[T_n]=\sigma_n[T_n]$. Write $\eta_L,\eta_U$ for the liminf and limsup of $-\log\alpha_n/n$, and $\zeta_L^c,\zeta_U^c$ for the liminf and limsup of $-\log\sigma_n[I-T_n]/n$. These are extended real values with natural logarithms. Choose any likelihood family $S_n(a)$ allowed by (6), including any effect on the zero subspace. An exponent evaluated at $a$ refers to this family; tests in operational optimizations range independently over all test sequences.
--
--   Put $B_e^*(r)=\inf\{\zeta_U^c[T]:\eta_L[T]\ge r\}$, $M=\sup_a\zeta_U^c(a)$, and $K=\inf_{a:\zeta_U^c(a)=M}(M-a)$, with empty infimum $+\infty$. For every real $r$,
--   $$
--   B_e^*(r)\le\inf_a\bigl(a+\max\{\eta_U(a),r\}\bigr).
--   $$
--   If $r\le K$, then
--   $$
--   B_e^*(r)\ge\inf_a\bigl(a+\max\{\eta_L(a),r\}\bigr).
--   $$
--   If every finite-block type-I exponent sequence converges, and either $M=+\infty$ or its plateau is empty, the latter expression equals $B_e^*(r)$ for every real $r$.
--
--   These give the upper bound, conditional lower bound, and all-rate validity of Han’s formula.
-- source:
--   An Information-Spectrum Approach to Classical and Quantum Hypothesis Testing for Simple Hypotheses, arXiv:quant-ph/0206185v2, PDF p. 15, Corollary 1: validity conditions for Han's formula (78)–(81)

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P46

noncomputable section

open Filter

open scoped BigOperators ENNReal NNReal

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

open QAlgorithms.Papers.Independent.Dependency50.P13 (IsPositive State relativeEntropy)

universe u

namespace QAlgorithms.Papers.Independent.Claimed50.P46

/-- Corollary 1, PDF pp.15–16, (78)–(81).
Printed: both max/positive-part forms and the cutoff M-sup{a:f(a)=M}.
Changed: use the displayed max form and inf{M-a:f(a)=M}, for finite real a.
Why: expanded positive-part arithmetic and infinite plateau subtraction can
cancel infinities. The finite formula and all-r clause (81) fix this convention. -/
theorem corollary1_han_validity (P : ℕ → SimpleHypothesisSystem.{u}) (hP : SwitchedNormalization P)
    (S : LikelihoodFamily P) :
    (∀ r : ℝ, correctTradeoff P true false r ≤ hanExpression (fun a => etaU (S.tests a)) r) ∧
    (∀ r : ℝ, (r : EReal) ≤ plateauThreshold (fun a => zetaUc (S.tests a)) →
      hanExpression (fun a => etaL (S.tests a)) r ≤ correctTradeoff P true false r) ∧
    ((∀ a : ℝ, Tendsto (fun k => blockErrorExponent k (testingTypeI (S.tests a k))) atTop
        (nhds (etaL (S.tests a)))) →
      (plateauHeight (fun a => zetaUc (S.tests a)) = ⊤ ∨
        ¬ ∃ a : ℝ, zetaUc (S.tests a) = plateauHeight (fun b => zetaUc (S.tests b))) →
      ∀ r : ℝ, correctTradeoff P true false r = hanExpression (fun a => etaL (S.tests a)) r) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P46

end
