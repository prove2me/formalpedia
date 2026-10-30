-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P05_arbitraryResourceDistillation
-- name    : QAlgorithms.Papers.Independent.Advance50.P05.arbitraryResourceDistillation
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T08:24:23.592438+00:00
-- url     : https://prove2.me/theorems/041a0709-b8d0-4e6c-8471-fcb0ffe46b89
-- title:
--   Exact asymptotic entanglement distillation from arbitrary resources
-- statement:
--   Let $H_A,H_B$ be positive-dimensional finite Hilbert spaces, and let $\widehat\rho=\{\rho_n^{AB}\}_{n\ge1}$ be any sequence of normalized states on $H_A^{\otimes n}\otimes H_B^{\otimes n}$. No independence, identical-copy, stationarity, symmetry, or purity assumption is imposed. All logarithms are base two. For assistance $a\in\{\to,\leftrightarrow\}$, let $E_D^a(\rho_n;\varepsilon)$ be the optimal logarithm of a positive integer MES rank obtainable by the corresponding actual LOCC protocol, with unconditional output root fidelity at least $1-\varepsilon$. Define
--   $$
--   E_{D,\infty}^a(\widehat\rho)=\lim_{\varepsilon\downarrow0}\liminf_{n\to\infty}\frac1n E_D^a(\rho_n;\varepsilon).
--   $$
--   For state sequences $r_n,s_n$ on the same finite spaces, put $\Delta_n(\gamma)=r_n-2^{n\gamma}s_n$ and
--   $$
--   \underline D(\widehat r\Vert\widehat s)=\sup\{\gamma\in\mathbb R:\liminf_n\operatorname{Tr}[\{\Delta_n(\gamma)\ge0\}\Delta_n(\gamma)]=1\},\qquad
--   \underline I^{C\to D}(\widehat r)=\min_{\widehat\sigma_D}\underline D(\widehat r\Vert\widehat{1}_C\otimes\widehat\sigma_D),
--   $$
--   where the minimum ranges over all sequences of normalized comparison states, without an identical-copy restriction. Then
--   $$
--   E_{D,\infty}^{\to}(\widehat\rho)=\max_{\widehat{\mathcal I}_A}\underline I^{A'\to BX}(\widehat\sigma),\qquad
--   E_{D,\infty}^{\leftrightarrow}(\widehat\rho)=\max_{\widehat\Lambda^{\leftrightarrow}}\underline I^{A'\to B'}(\widehat\nu).
--   $$
--   Here $\sigma_n=\sum_x(\mathcal E_{n,x}\otimes\mathrm{id}_B)(\rho_n)\otimes|x\rangle\langle x|$ is the full output of Alice's CP instrument, with $X$ held by Bob, and $\nu_n=\Lambda_n^{\leftrightarrow}(\rho_n)$ is an actual two-way LOCC output. Output dimensions, outcome counts and protocol lengths may vary with $n$. Both maxima and the comparison minima are attained: a maximizing sequence has the stated value and bounds every competing sequence from above.
--
--   The result characterizes distillation for arbitrary resources through spectral inf-coherent information. **Formalization Note:** block index $k$ represents $n=k+1$; extended extrema preserve infinite values, and actual right-limit convergence is included. Two-way LOCC uses the plan's arbitrary finite adaptive-protocol convention.
-- source:
--   Distilling entanglement from arbitrary resources, arXiv:1006.1896v2, PDF p. 13, Theorem 1, Eqs.(47)–(48): exact asymptotic distillation from arbitrary resources

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P05

noncomputable section

namespace QAlgorithms.Papers.Independent.Advance50.P05

open QAlgorithms Filter

open scoped Matrix ComplexConjugate ComplexOrder

open QAlgorithms.Papers.Independent.Dependency50.P19 (first both epr IsIso)

open QAlgorithms.Papers.Independent.Information100.P07 (support)

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower SupportIncluded)

open QAlgorithms.Papers.Independent.Dependency50.P35 (elog marginalAB marginalAC)

open QAlgorithms.Papers.Independent.Support50.P21 (dMin weakPositive PositiveTensorBasis)

open QAlgorithms.Papers.Independent.Information100.P21 (FiniteLOCC)

open QAlgorithms.Papers.Independent.Information100.P67 (IsSubnormalized)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Buscemi--Datta, arXiv:1006.1896v2, PDF pp.12--13, Theorem 1, (47)--(48).
Both arbitrary-resource formulas, including actual right limits, attained
maximizing preprocessing sequences, and attained comparison-state minima.
No direct one-shot bound is assumed as a hypothesis. -/
theorem arbitraryResourceDistillation
    {A B : Type} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    (rho : (k : ℕ) → Matrix (PositiveTensorBasis A k × PositiveTensorBasis B k)
      (PositiveTensorBasis A k × PositiveTensorBasis B k) ℂ)
    (hrho : ∀ k, IsDensityMatrix (rho k)) :
    Tendsto (asymptoticInner .forward rho) (nhdsWithin 0 (Set.Ioi 0))
      (nhds (asymptoticDistillable .forward rho)) ∧
    Tendsto (asymptoticInner .twoWay rho) (nhdsWithin 0 (Set.Ioi 0))
      (nhds (asymptoticDistillable .twoWay rho)) ∧
    (∃ P : (k : ℕ) → AlicePreprocessing (PositiveTensorBasis A k),
      asymptoticDistillable .forward rho = forwardSequenceScore rho P ∧
      (∀ Q, forwardSequenceScore rho Q ≤ forwardSequenceScore rho P) ∧
      SpectralMinimumAttained (fun k => (P k).output (rho k))) ∧
    (∃ P : (k : ℕ) → TwoWayPreprocessing (PositiveTensorBasis A k) (PositiveTensorBasis B k),
      asymptoticDistillable .twoWay rho = twoWaySequenceScore rho P ∧
      (∀ Q, twoWaySequenceScore rho Q ≤ twoWaySequenceScore rho P) ∧
      SpectralMinimumAttained (fun k => (P k).operation (rho k))) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P05

end
