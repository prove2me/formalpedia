-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P46_theorem6_fixed_length_rates
-- name    : QAlgorithms.Papers.Independent.Claimed50.P46.theorem6_fixed_length_rates
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T11:30:01.514026+00:00
-- url     : https://prove2.me/theorems/7615cd77-832c-471c-8d4e-b6cbaf3f095c
-- title:
--   Theorem 6: fixed-length operational rates (96)–(106)
-- statement:
--   Let $P_n$ be a general source on a finite or countable alphabet $X^n$, with no independence or stationarity assumption. A code has a finite nonempty message set and arbitrary stochastic encoder and decoder, each normalized on every input. Write $\gamma_n$ for its error probability, $q_n=1-\gamma_n$ for success, and $L(\Phi)=\limsup_n n^{-1}\log|\Phi_n|$ for its extended real rate. Infima below range over all such code sequences. The counting-measure testing model compares $\rho_n=P_n$ with $\sigma_n(x)=1$. Choose any allowed likelihood family. Write $t_n(a)=\rho_n[I-S_n(-a)]$ for the upper self-information tail with its matched boundary choice; its complement is the matched lower tail. Logarithms are natural and zero probability has infinite exponent.
--
--   Define $R(\varepsilon)=\inf\{L(\Phi):\limsup\gamma_n\le\varepsilon\}$, $R^\dagger(\varepsilon)=\inf\{L(\Phi):\liminf\gamma_n<\varepsilon\}$, and $R_e(r)=\inf\{L(\Phi):\liminf(-\log\gamma_n)/n\ge r\}$. Let $B,B^\dagger,B_e,D_L,D_U$ be the counting-measure testing optima and spectral rates. Then
--   $$
--   R(\varepsilon)=-B(\varepsilon)=-D_L(\varepsilon)=\inf\{a:\limsup t_n(a)\le\varepsilon\}\quad(0\le\varepsilon<1),
--   $$
--   $$
--   R^\dagger(\varepsilon)=-B^\dagger(\varepsilon)=-D_U(\varepsilon)=\inf\{a:\liminf t_n(a)<\varepsilon\}\quad(0\le\varepsilon\le1).
--   $$
--   Writing $\overline H=\inf\{a:t_n(a)\to0\}$ and $\underline H=\sup\{a:t_n(a)\to1\}$,
--   $$
--   R(0)=\overline H=\inf\{R:\exists\Phi,\ L(\Phi)\le R,\ \gamma_n\to0\},
--   $$
--   $$
--   R^\dagger(1)=\underline H=\sup\{R:\forall\Phi,\ L(\Phi)\le R\Rightarrow\gamma_n\to1\}.
--   $$
--   For $r>0$, put $\sigma_L(a)=\liminf_n[-\log t_n(a)]/n=\eta_L(-a)$. Then
--   $$
--   R_e(r)=-B_e(r)=\sup_{a:\sigma_L(a)<r}(a-\sigma_L(a)).
--   $$
--   The operational endpoint values are $R(1)=R_e(0)=0$, $R^\dagger(0)=+\infty$.
--
--   These are all fixed-length rate identities with their necessary endpoint domains.
-- source:
--   An Information-Spectrum Approach to Classical and Quantum Hypothesis Testing for Simple Hypotheses, arXiv:quant-ph/0206185v2, PDF p. 18, Theorem 6: fixed-length operational rates (96)–(106)

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P46

noncomputable section

open Filter

open scoped BigOperators ENNReal NNReal

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

open QAlgorithms.Papers.Independent.Dependency50.P13 (IsPositive State relativeEntropy)

universe u

namespace QAlgorithms.Papers.Independent.Claimed50.P46

/-- Theorem 6, PDF p.18, (96)–(106). Printed parameter ranges are omitted.
Changed: (96) requires eps<1 and (104) r>0 for nonempty codes.
Why: R(1)=Re(0)=0 whereas -B(1)=-Be(0)=-infinity.
The dagger identities (98)–(99) retain eps=0: all sides are +infinity
because their strict admissibility sets are empty. -/
theorem theorem6_fixed_length_rates (P : Source.{u}) (S : LikelihoodFamily (sourceSystem P)) :
    (∀ eps : ℝ, 0 ≤ eps → eps < 1 →
      compressionRate P false eps = -steinB (sourceSystem P) eps ∧
      compressionRate P false eps = -divergenceL S eps ∧
      compressionRate P false eps = sInf {z | ∃ a : ℝ, z = (a : EReal) ∧
        limsup (sourceTail S a) atTop ≤ ENNReal.ofReal eps}) ∧
    (∀ eps : ℝ, 0 ≤ eps → eps ≤ 1 →
      compressionRate P true eps = -steinBdag (sourceSystem P) eps ∧
      compressionRate P true eps = -divergenceU S eps ∧
      compressionRate P true eps = sInf {z | ∃ a : ℝ, z = (a : EReal) ∧
        liminf (sourceTail S a) atTop < ENNReal.ofReal eps}) ∧
    compressionRate P false 0 = spectralEntropy S true ∧
    compressionRate P false 0 = sInf {z | ∃ R : ℝ, z = (R : EReal) ∧
      ∃ C : (k : ℕ) → StochasticSourceCode (P.X k), codeRate P C ≤ (R : EReal) ∧
        Tendsto (fun k => sourceCodeError P k (C k)) atTop (nhds 0)} ∧
    compressionRate P true 1 = spectralEntropy S false ∧
    compressionRate P true 1 = sSup {z | ∃ R : ℝ, z = (R : EReal) ∧
      ∀ C : (k : ℕ) → StochasticSourceCode (P.X k), codeRate P C ≤ (R : EReal) →
        Tendsto (fun k => sourceCodeError P k (C k)) atTop (nhds 1)} ∧
    (∀ r : ℝ, 0 < r → codingErrorRate P r = -errorTradeoff (sourceSystem P) r ∧
      codingErrorRate P r = sSup {z | ∃ a : ℝ, sourceSigmaL S a < (r : EReal) ∧
        z = (a : EReal) - sourceSigmaL S a}) ∧
    (∀ a : ℝ, sourceSigmaL S a = etaL (S.tests (-a))) ∧
    compressionRate P false 1 = 0 ∧ codingErrorRate P 0 = 0 ∧ compressionRate P true 0 = ⊤ := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P46

end
