-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P46_coding_strong_converse
-- name    : QAlgorithms.Papers.Independent.Claimed50.P46.coding_strong_converse
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T11:30:42.189272+00:00
-- url     : https://prove2.me/theorems/df0f4bd3-c63e-4979-a9b4-08635994034e
-- title:
--   Remark 14: source strong converse iff spectral entropies coincide
-- statement:
--   Let $P_n$ be a general source on a finite or countable alphabet $X^n$, with no independence or stationarity assumption. A code has a finite nonempty message set and arbitrary stochastic encoder and decoder, each normalized on every input. Write $\gamma_n$ for its error probability, $q_n=1-\gamma_n$ for success, and $L(\Phi)=\limsup_n n^{-1}\log|\Phi_n|$ for its extended real rate. Infima below range over all such code sequences. The counting-measure testing model compares $\rho_n=P_n$ with $\sigma_n(x)=1$. Choose any allowed likelihood family. Write $t_n(a)=\rho_n[I-S_n(-a)]$ for the upper self-information tail with its matched boundary choice; its complement is the matched lower tail. Logarithms are natural and zero probability has infinite exponent.
--
--   Let $R=R(0)$, $R^\dagger=R^\dagger(1)$, and let $\overline H,\underline H$ be the spectral sup- and inf-entropies. Then
--   $$
--   [\forall\Phi,\ L(\Phi)<R\Rightarrow\gamma_n\to1]
--   \quad\Longleftrightarrow\quad R=R^\dagger
--   \quad\Longleftrightarrow\quad \overline H=\underline H.
--   $$
--
--   This characterizes the strong converse for a general source.
-- source:
--   An Information-Spectrum Approach to Classical and Quantum Hypothesis Testing for Simple Hypotheses, arXiv:quant-ph/0206185v2, PDF p. 18, Remark 14: source strong converse iff spectral entropies coincide

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P46

noncomputable section

open Filter

open scoped BigOperators ENNReal NNReal

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

open QAlgorithms.Papers.Independent.Dependency50.P13 (IsPositive State relativeEntropy)

universe u

namespace QAlgorithms.Papers.Independent.Claimed50.P46

/-- Remark 14, PDF p.18: both the operational and spectral strong-converse equivalences. -/
theorem coding_strong_converse (P : Source.{u}) (S : LikelihoodFamily (sourceSystem P)) :
    ((∀ C : (k : ℕ) → StochasticSourceCode (P.X k), codeRate P C < compressionRate P false 0 →
      Tendsto (fun k => sourceCodeError P k (C k)) atTop (nhds 1)) ↔
      compressionRate P false 0 = compressionRate P true 1) ∧
    (compressionRate P false 0 = compressionRate P true 1 ↔
      spectralEntropy S true = spectralEntropy S false) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P46

end
