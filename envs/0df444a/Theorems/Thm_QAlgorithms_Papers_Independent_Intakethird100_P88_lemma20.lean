-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P88_lemma20
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P88.lemma20
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T04:15:38.406323+00:00
-- url     : https://prove2.me/theorems/5e3b52bc-eb34-44f1-aa74-130d8ec97333
-- title:
--   Six variational formulas for measured relative entropy on trace-class operators
-- statement:
--   Let $H$ be a possibly infinite-dimensional complex Hilbert space, $\rho$ a positive trace-class operator of trace one, and $\sigma$ a nonzero positive trace-class operator, with no normalization condition on $\sigma$. Define $D_M(\rho\|\sigma)$ as the supremum of classical base-two relative entropies over all finite-outcome POVMs. This quantity is extended real and may be negative. Write $\mathcal B_{\mathrm{sa}}(H)$ for the bounded self-adjoint operators, $L>0$ for strict positivity on every nonzero vector, and $L\ge\delta I$ for some $\delta>0$ for a uniform positive lower spectral bound. Then
--
--   $$
--   \begin{aligned}
--   D_M(\rho\|\sigma)
--   &=\sup_{h\in\mathcal B_{\mathrm{sa}}}\{\operatorname{Tr}(\rho h)-\log_2\operatorname{Tr}(\sigma 2^h)\}\\
--   &=\sup_{h\in\mathcal B_{\mathrm{sa}}}\{\operatorname{Tr}(\rho h)+\log_2(e)(1-\operatorname{Tr}(\sigma 2^h))\}\\
--   &=\sup_{L\in\mathcal B_{\mathrm{sa}},\,L\ge\delta I,\,\delta>0}\{\operatorname{Tr}(\rho\log_2L)-\log_2\operatorname{Tr}(\sigma L)\}\\
--   &=\sup_{L\in\mathcal B_{\mathrm{sa}},\,L\ge\delta I,\,\delta>0}\{\operatorname{Tr}(\rho\log_2L)+\log_2(e)(1-\operatorname{Tr}(\sigma L))\}\\
--   &=\sup_{L\in\mathcal B_{\mathrm{sa}},\,L>0}\{\operatorname{Tr}(\rho\log_2L)-\log_2\operatorname{Tr}(\sigma L)\}\\
--   &=\sup_{L\in\mathcal B_{\mathrm{sa}},\,L>0}\{\operatorname{Tr}(\rho\log_2L)+\log_2(e)(1-\operatorname{Tr}(\sigma L))\}.
--   \end{aligned}
--   $$
--
--   In the middle two programs the positive constant $\delta$ may depend on $L$. The last two programs allow logarithmic expectations equal to $-\infty$. These identities provide variational programs for measured relative entropy without imposing entropy or energy bounds.
-- source:
--   Asymptotic state transformations of continuous variable resources, arXiv:2010.00044v3, PDF p. 11, IV C: Lemma20

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P88

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P88

open Filter

open QAlgorithms.Papers.Independent.Dependency50.P13

open QAlgorithms.Papers.Independent.Dependency50.P39 (Fock fockKet fockDyad)

open QAlgorithms.Papers.Independent.Information100.P62 (logTwo)

attribute [local instance] Classical.propDecidable

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- PDF p.11, Lemma 20, (23)–(28), with positivity regimes explained on p.18.
All six variational expressions are retained. The second operator is nonzero
and positive trace-class, and is not required to have trace one.
Source correction in its measured-entropy dependency: printed (10), p.5,
uses P_rho twice; changed the second to P_sigma, exactly as the proof on
pp.19-20 does. The literal repeated distribution would give zero identically. -/
theorem lemma20 {I : Type*} (b : HilbertBasis I ℂ H) (rho : State b)
    (sigma : PositiveTraceClass H) (hsigma : sigma.val.val ≠ 0) :
    traceClassMeasuredEntropyBits b rho sigma = exponentialProgram b rho sigma false ∧
    traceClassMeasuredEntropyBits b rho sigma = exponentialProgram b rho sigma true ∧
    traceClassMeasuredEntropyBits b rho sigma = positiveProgram b rho sigma true false ∧
    traceClassMeasuredEntropyBits b rho sigma = positiveProgram b rho sigma true true ∧
    traceClassMeasuredEntropyBits b rho sigma = positiveProgram b rho sigma false false ∧
    traceClassMeasuredEntropyBits b rho sigma = positiveProgram b rho sigma false true := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P88

end
