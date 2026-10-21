-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P17_entropy_power_beamSplitter
-- name    : QAlgorithms.Papers.Independent.Next46.P17.entropy_power_beamSplitter
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T13:21:43.729797+00:00
-- url     : https://prove2.me/theorems/0035b4d9-3e73-446a-9286-08ad2df4d563
-- title:
--   Entropy power inequality for the 50:50 beam splitter
-- statement:
--   Let $n\geq1$ and let $\rho_X,\rho_Y$ be arbitrary normalized states of $n$ bosonic modes on the full Hilbert space. Write $\mathcal E_{1/2}$ for a 50:50 beam splitter followed by discarding its second output. Entropy $S$ uses natural logarithms and may be infinite, with $e^{+\infty}=+\infty$. Then
--
--   $$
--   e^{S(\mathcal E_{1/2}(\rho_X\otimes\rho_Y))/n}\geq\frac12e^{S(\rho_X)/n}+\frac12e^{S(\rho_Y)/n}.
--   $$
--
--   This is the paper's entropy power inequality for independent quantum inputs. Its exponent is $S/n$.
-- source:
--   The entropy power inequality for quantum systems, arXiv:1205.3409v2, PDF p. 12, Theorem VII.2, (89); paper-level seed pp.1–2

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P17

noncomputable section

open Filter MeasureTheory

open scoped ENNReal BigOperators Topology

namespace QAlgorithms.Papers.Independent.Next46.P17

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Dependency50.P33
  (State IsTraceClass IsTraceClassChannel productCoeff tensorApply)

open QAlgorithms.Papers.Independent.Frontier18.P07
  (extendedEntropyNats extendedRelativeEntropyNats)

open QAlgorithms.Papers.Independent.Claimed50.P19 (productWeyl FiniteMeanEnergy PhysicalCovariance Cov FockIndex covarianceCharacteristicValue)

open QAlgorithms.Papers.Independent.Frontier30.P08 (interleavedSymplecticForm)

/-- PDF p.12, Theorem VII.2, (89), restating the pp.1–2 paper-level seed.
There is no factor two in the exponent. The result concerns the 50:50 beam
splitter and arbitrary states, including infinite-entropy inputs. Proof p.13
has the reversed sign in (95) and suppresses a positive EZ factor later;
neither typo changes this theorem's displayed conclusion. -/
theorem entropy_power_beamSplitter {n : ℕ} (hn : 0 < n)
    (rhoX rhoY : State (FockIndex n)) :
    ENNReal.ofReal (1 / 2 : ℝ) * bosonicEntropyPower n (extendedEntropyNats rhoX.coefficients) +
      ENNReal.ofReal (1 / 2 : ℝ) * bosonicEntropyPower n (extendedEntropyNats rhoY.coefficients) ≤
    bosonicEntropyPower n (extendedEntropyNats (beamSplitter (1 / 2 : ℝ)
      (productCoeff rhoX.coefficients rhoY.coefficients))) := by sorry

end QAlgorithms.Papers.Independent.Next46.P17

end
