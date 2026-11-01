-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P76_photonOccupationCoding
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P76.photonOccupationCoding
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T07:51:23.211004+00:00
-- url     : https://prove2.me/theorems/f1916ad1-80e8-40bd-9e47-72e4edfd8a5a
-- title:
--   Coherent coding with exponentially small averaged photon leakage
-- statement:
--   Fix $N_S>0$ and $0<\delta_1<N_S$ for the identity-transmissivity coherent-state channel. There is $q\in(0,1)$, depending on these energy parameters, such that for every $0<\varepsilon<1$ and $\delta_2>0$ there are $C>0$ and $N\ge2$ with the following property for every integer $n\ge N$. One has $q^{n/2}+\varepsilon^{\delta_2}<1$, and there exists a deterministic code of $M\ge1$ equiprobable coherent product signals with one joint POVM, average decoding error at most $\varepsilon$, and
--
--   $$
--   \log_2M\ge ng(N_S-\delta_1)+\sqrt{nv(N_S-\delta_1)}\,\Phi^{-1}(\varepsilon^{1+\delta_2})-C\log_2n,
--   \qquad
--   \operatorname{Tr}\bigl[(I-\Pi_{\le\lceil nN_S\rceil})\bar\rho_{\rm code}\bigr]\le q^{n/2}.
--   $$
--
--   Here $\bar\rho_{\rm code}$ is the uniform average of the input density operators, $\Pi$ cuts off total photon number across all $n$ modes, $g$ is thermal entropy in bits, and $v$ is thermal entropy variance in bits squared. This is simultaneous decodability and exponentially vanishing occupation leakage, distinct from a mean-energy constraint.
-- source:
--   Second-order coding rates for pure-loss bosonic channels, arXiv:1408.5328v3, PDF p. 11, §6.1, (6.10)–(6.11)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P76

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P76

open MeasureTheory Filter

open QAlgorithms.Papers.Independent.Information100.P63 (logTwo normalCDF normalQuantile)

open QAlgorithms.Papers.Independent.Information100.P54 (thermalEntropy)

open QAlgorithms.Papers.Independent.Dependency50.P39 (coherentCoefficient)

open QAlgorithms.Papers.Independent.Next46.P32 (PositiveKernel)

open scoped BigOperators ENNReal Topology

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

/-- PDF p.11, (6.10)–(6.11): at eta=1 there are actual finite coherent-state
codes with average error <=epsilon and exponentially small total-photon leakage.
The auxiliary error is epsilon^(1+delta2). The tail constant depends only on NS
and delta1, before blocklength; it is not an assumed tail bound on the code.
The rate and occupation claims are simultaneous, with cutoff ceil(n NS). -/
theorem photonOccupationCoding (NS delta1 : ℝ)
    (hNS : 0 < NS) (hd1 : 0 < delta1) (hd1NS : delta1 < NS) :
    ∃ q : ℝ, 0 < q ∧ q < 1 ∧ ∀ epsilon delta2 : ℝ,
      0 < epsilon → epsilon < 1 → 0 < delta2 →
      ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, 2 ≤ N ∧ ∀ n : ℕ, N ≤ n →
        q ^ ((n : ℝ) / 2) + epsilon ^ delta2 < 1 ∧
        ∃ (M : ℕ) (c : PureCQCode (Fin n → ℂ) (Fin n → ℕ) M),
          pureCQAverageError (coherentChannel n) c ≤ epsilon ∧
          photonLeakage c NS ≤ q ^ ((n : ℝ) / 2) ∧
          (n : ℝ) * thermalEntropy (NS - delta1) +
            Real.sqrt ((n : ℝ) * thermalDispersion (NS - delta1)) *
              normalQuantile (epsilon ^ (1 + delta2)) - C * logTwo (n : ℝ) ≤
            logTwo (M : ℝ) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P76

end
