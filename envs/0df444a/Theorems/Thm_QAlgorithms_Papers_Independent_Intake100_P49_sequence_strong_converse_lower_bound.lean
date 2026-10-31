-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P49_sequence_strong_converse_lower_bound
-- name    : QAlgorithms.Papers.Independent.Intake100.P49.sequence_strong_converse_lower_bound
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T13:44:24.685118+00:00
-- url     : https://prove2.me/theorems/da7474da-29e7-4fa1-a00d-c30f2a1502cf
-- title:
--   Strong-converse lower bound for arbitrary operator sequences
-- statement:
--   Let $(\mathcal H_n,\rho_n,\sigma_n)_{n\ge1}$ be arbitrary complex separable complete Hilbert spaces with nonzero bounded PSD pairs, and let $r\in\mathbb R$.
--
--   For a test sequence $0\le T_n\le I$ set $\gamma_n=\operatorname{Tr}(T_n^{1/2}\rho_nT_n^{1/2})$ and $\beta_n=\operatorname{Tr}(T_n^{1/2}\sigma_nT_n^{1/2})$. The lower, upper and existing-limit strong-converse exponents are the infima of respectively $\liminf$, $\limsup$ and existing extended limits of $-n^{-1}\log\gamma_n$, subject in every case to $\liminf -n^{-1}\log\beta_n\ge r$. Define $\widetilde\psi_{\mathrm{seq}}(u)=\limsup_n n^{-1}\widetilde\psi(\rho_n\Vert\sigma_n|u)$ where for $0<u<1$ the single-system perspective is $(1-u)\log Q^*_{1/(1-u)}$, and its values at $u=0,1$ are respectively $\log\operatorname{Tr}\rho_n$ and $D_{\max}(\rho_n\Vert\sigma_n)$, and $\widehat H_r^*=\sup_{0\le u\le1}\{ur-\widetilde\psi_{\mathrm{seq}}(u)\}$. Then $$\widehat H_r^*\le\underline{\mathrm{sc}}_r\le\overline{\mathrm{sc}}_r\le\mathrm{sc}_r.$$ All limits and infima are extended. Zero tests are allowed; $\log0=-\infty$. This applies without an iid or trace-finiteness assumption.
-- source:
--   The strong converse exponent of discriminating infinite-dimensional quantum states, arXiv:2107.08036v5, PDF p. 28, Proposition IV.1

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P49

noncomputable section

open Filter

open scoped ENNReal NNReal BigOperators

namespace QAlgorithms.Papers.Independent.Intake100.P49

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Dependency50.P13
  (IsPositive IsTraceClass TraceClass traceNormTopology)

open QAlgorithms.Papers.Independent.Bridge50.P48 (hilbertPositiveTrace)

variable {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Proposition IV.1, PDF p.28, (IV.103): non-iid, unnormalized binary
operator sequences. All three strong-converse exponents use the same constraint. -/
theorem sequence_strong_converse_lower_bound (S : BinarySequence) (r : ℝ) :
    sequenceHatHoeffding S r ≤ lowerSC S r ∧ lowerSC S r ≤ upperSC S r ∧
      upperSC S r ≤ limitSC S r := by sorry

end QAlgorithms.Papers.Independent.Intake100.P49

end
