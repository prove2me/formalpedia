-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P54_nds_discrimination
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P54.nds_discrimination
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T06:02:24.896186+00:00
-- url     : https://prove2.me/theorems/0c945955-e67e-4729-8413-d53482214154
-- title:
--   NDS exact discrimination and optimal loss-sector receiver
-- statement:
--   Let $M\ge1$ be the finite number of signal modes and $J\ge0$ the finite number of retained idler modes, on the full optical Fock spaces. The two channels have equal priors, independent vacuum environments, reflectances $0\le R_0\le R_1\le1$, field magnitudes $r_b=\sqrt{R_b}$ and $t_b=\sqrt{1-R_b}$, and distinct complex reflection coefficients $r_b e^{i\theta_b}$. Every signal mode sees the same channel; idlers are retained losslessly and environment outputs are inaccessible. Write $\mathcal F$ for squared Uhlmann fidelity, $P_e$ for minimum average error over all joint binary receivers, $Q_s=\operatorname{Tr}(\rho_0^s\rho_1^{1-s})$, and $Q=\min_{0\le s\le1}Q_s$, with zero powers interpreted as support projections.
--
--   Let the normalized pure probe be NDS: its signal marginal is diagonal in the multimode occupation basis. For each lost occupation string $\mathbf k$, let $v_{b,\mathbf k}$ be the unnormalized retained vector constructed by the vacuum splitter, $p_{b,\mathbf k}=\|v_{b,\mathbf k}\|^2$, $I_{\mathbf k}=\langle v_{0,\mathbf k},v_{1,\mathbf k}\rangle$, and $H_{\mathbf k}=\operatorname{span}\{v_{0,\mathbf k},v_{1,\mathbf k}\}$. These blocks are mutually orthogonal and have dimension at most two. Moreover $p_{b,\mathbf k}=\sum_{\mathbf n}p_{\mathbf n}|A_{\mathbf n;\mathbf k}^{(b)}|^2$, with a convergent sum and $A=0$ unless $\mathbf k\le\mathbf n$ componentwise. Then $|I_{\mathbf k}|^2\le p_{0,\mathbf k}p_{1,\mathbf k}$, and the convergent exact-error formula is
--
--   $$P_e=\frac12-\frac14\sum_{\mathbf k}\sqrt{(p_{0,\mathbf k}+p_{1,\mathbf k})^2-4|I_{\mathbf k}|^2}.$$
--
--   An attaining projective receiver first resolves the orthogonal loss blocks and then decides zero on the positive spectrum of $|v_{0,\mathbf k}\rangle\langle v_{0,\mathbf k}|-|v_{1,\mathbf k}\rangle\langle v_{1,\mathbf k}|$ and one on its negative spectrum. Zero eigenspaces admit arbitrary projective ties; the complement of all blocks has probability zero. For priors $\pi_b\ge0$ with $\pi_0+\pi_1=1$, the same blocks support the weighted spectral receiver and $P_e=(1-\|\pi_0\rho_0-\pi_1\rho_1\|_1)/2$.
--
--   The block receiver specifies an abstract optimum even in degenerate sectors, without dividing by a zero sector probability.
-- source:
--   Discriminating quantum-optical beam-splitter channels with number-diagonal signal states: Applications to quantum reading and target detection, arXiv:1105.4063v3, PDF p. 5, nds-discrimination

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P54

noncomputable section

open scoped BigOperators ComplexConjugate

open MeasureTheory Filter

namespace QAlgorithms.Papers.Independent.Intakethird100.P54

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)

open QAlgorithms.Papers.Independent.Dependency50.P39 (coherentCoefficient)

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

/-- Exact NDS discrimination and an attaining complete block receiver, PDF pp.4–5,
(25)–(42), and [22], p.13. Blocks have dimension AT MOST two; zero eigenvalues
are assigned arbitrary projective ties, correcting the source's degenerate-block prose. -/
theorem nds_discrimination {M J : ℕ} (hM : 0 < M) (c : Channels) (hc : ValidSplitters c)
    (psi : Hilbert (Occupation (Fin J) × Occupation (Fin M))) (hpsi : ‖psi‖ = 1)
    (hnds : IsNDS psi) :
    (∀ k, Module.Finite ℂ (lossBlock c psi k) ∧
      Module.finrank ℂ (lossBlock c psi k) ≤ 2) ∧
    (∀ k l, k ≠ l → ∀ u ∈ lossBlock c psi k, ∀ v ∈ lossBlock c psi l,
      inner ℂ u v = 0) ∧
    (∀ b k, Summable (fun n => signalLaw psi n * Complex.normSq (lossAmplitude (c b) n k)) ∧
      lossProbability c psi b k = ∑' n, signalLaw psi n * Complex.normSq (lossAmplitude (c b) n k)) ∧
    (∀ k, Complex.normSq (lossOverlap c psi k) ≤
      lossProbability c psi false k * lossProbability c psi true k) ∧
    Summable (fun k => Real.sqrt ((lossProbability c psi false k +
      lossProbability c psi true k)^2 - 4*Complex.normSq (lossOverlap c psi k))) ∧
    outputError c psi = 1/2 - (1/4) * ∑' k,
      Real.sqrt ((lossProbability c psi false k + lossProbability c psi true k)^2 -
        4*Complex.normSq (lossOverlap c psi k)) ∧
    (∃ E, BlockReceiver c psi 1 1 E ∧
      sectorRisk c psi E (1/2) (1/2) = outputError c psi) ∧
    (∀ v : Hilbert (Occupation (Fin J) × Occupation (Fin M)),
      (∀ k, ∀ w ∈ lossBlock c psi k, inner ℂ w v = 0) →
      ∀ b, (∑' k, Complex.normSq (inner ℂ (lossSector (c b) psi k) v)) = 0) ∧
    (∀ pi0 pi1 : ℝ, 0 ≤ pi0 → 0 ≤ pi1 → pi0+pi1=1 →
      bayesError (returned (c false) psi) (returned (c true) psi) pi0 pi1 =
        (1-weightedTraceNorm (returned (c false) psi) (returned (c true) psi) pi0 pi1)/2 ∧
      ∃ E, BlockReceiver c psi pi0 pi1 E ∧
        sectorRisk c psi E pi0 pi1 =
          bayesError (returned (c false) psi) (returned (c true) psi) pi0 pi1) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P54

end
