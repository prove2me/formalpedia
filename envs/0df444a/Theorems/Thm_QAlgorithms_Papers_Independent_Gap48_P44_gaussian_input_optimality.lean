-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P44_gaussian_input_optimality
-- name    : QAlgorithms.Papers.Independent.Gap48.P44.gaussian_input_optimality
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T05:45:19.055372+00:00
-- url     : https://prove2.me/theorems/f7731151-32fe-416a-8cf1-ba8bde9270a7
-- title:
--   Gaussian conditional-input optimization is exact without a conjecture
-- statement:
--   Write $g_n(x)=(x+1)\ln(x+1)-x\ln x$ and $g_b(x)=g_n(x)/\ln2$ for $x\ge0$, with $0\ln0=0$. Fix $\eta\in[1/2,1]$ and $N_S\ge0$. For every $n\ge1$ and normalized finite ensemble of Gaussian $n$-mode conditional states with unconditional total photon energy at most $nN_S$, all four common-parameter inequalities (60)–(63) hold for one $\lambda\in[0,1]$, without the unrestricted minimum-output-entropy conjecture. Intra-block Gaussian correlations are permitted, and the unconditional mixture need not be Gaussian.
--
--   Let $\mathcal G_{\eta,N_S}$ be the closure of the union, over all positive blocklengths and all such finite ensembles, of the per-use entropy regions (3)–(5). Then
--
--   $$\mathcal G_{\eta,N_S}=\bigcup_{0\le\lambda\le1}\left\{(C,Q,E)\in\mathbb R^3:\begin{aligned}C+2Q&\le g_b(\lambda N_S)+g_b(\eta N_S)-g_b((1-\eta)\lambda N_S),\\Q+E&\le g_b(\eta\lambda N_S)-g_b((1-\eta)\lambda N_S),\\C+Q+E&\le g_b(\eta N_S)-g_b((1-\eta)\lambda N_S)\end{aligned}\right\}.$$
--
--   The rates are signed net generated resources per use. The restriction concerns the input-state optimization; it does not define a class of codes using only Gaussian gates. Closure retains the displaced-thermal continuum through finite-alphabet approximation.
-- source:
--   Quantum trade-off coding for bosonic communication, arXiv:1105.0119v4, PDF p. 11, §III G: Gaussian-input restricted optimum without conjecture

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P44

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P44

open Filter

open scoped ENNReal Topology

open QAlgorithms.Papers.Independent.Claimed50.P39 (g)

open QAlgorithms.Papers.Independent.Information100.P54 (thermalEntropy)

/-- PDF pp.11-13, Section III G: Gaussian conditional inputs need no
unrestricted minimum-output-entropy premise. The same lambda satisfies all four
announced block bounds, and the regularized Gaussian entropy optimization is
exactly the complete three-face family. Gaussian correlations are retained and
no Gaussian assumption is imposed on the unconditional mixture. -/
theorem gaussian_input_optimality (eta budget : ℝ)
    (heta0 : (1 / 2 : ℝ) ≤ eta) (heta1 : eta ≤ 1) (hbudget : 0 ≤ budget) :
    (∀ (n : ℕ), 0 < n → ∀ {X : Type} [Fintype X] (e : BlockEnsemble X n),
      (∀ x, Fock.Gaussian (e.state x).coefficients) →
      e.energy ≤ ENNReal.ofReal ((n : ℝ) * budget) →
      ∃ share ∈ Set.Icc (0 : ℝ) 1,
        e.entropyAverage id ≤ ENNReal.ofReal ((n : ℝ) * thermalEntropy (share * budget)) ∧
        blockEntropy (Fock.pureLoss n eta e.average) ≤
          ENNReal.ofReal ((n : ℝ) * thermalEntropy (eta * budget)) ∧
        e.entropyAverage (Fock.pureLoss n eta) ≤
          ENNReal.ofReal ((n : ℝ) * thermalEntropy (eta * share * budget)) ∧
        ENNReal.ofReal ((n : ℝ) * thermalEntropy ((1 - eta) * share * budget)) ≤
          e.entropyAverage (lossComplement n eta)) ∧
    gaussianDynamicOptimization eta budget = lossQuantumFamily eta budget := by sorry

end QAlgorithms.Papers.Independent.Gap48.P44

end
