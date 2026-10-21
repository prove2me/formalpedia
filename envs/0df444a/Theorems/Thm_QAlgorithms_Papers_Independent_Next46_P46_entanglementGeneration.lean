-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P46_entanglementGeneration
-- name    : QAlgorithms.Papers.Independent.Next46.P46.entanglementGeneration
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T15:02:29.636183+00:00
-- url     : https://prove2.me/theorems/4adb31ad-6319-4b81-88d4-40949b9ab5d3
-- title:
--   Coherent private coding generates entanglement
-- statement:
--   Fix an isometry $U:A'\to BE$, an orthonormal input family $(|v_x\rangle)_x$, and a probability law $P$. Let $R$ be the coherent information of the source obtained by sending the second register of $\sum_x\sqrt{P(x)}|x\rangle|v_x\rangle$ through $U$.
--
--   For every $\varepsilon,\delta>0$ and every sufficiently large positive $n$, one can choose positive integers $M,S,D$, distinct words $u^{ms}$, unit-modulus phases $\alpha_{ms}$, a coherent Bob decoder with a retained $D$-dimensional payload, an isometric embedding of the original Bob payload, and message-controlled residual unitaries. The actual preparation is
--
--   $$
--   \frac1{\sqrt{MS}}\sum_{m,s}\alpha_{ms}|m\rangle^A|v_{u^{ms}}\rangle^{(A')^n},\qquad
--   \frac{\log_2M}{n}\ge R-\delta,
--   $$
--
--   where $|v_{u}\rangle=\bigotimes_i|v_{u_i}\rangle$. Before correction its output is within trace-norm error $\varepsilon$ of the corresponding equation-(5) state: both parties carry $m$, Bob also carries $s$, and the embedded residual is the actual dilated word $U^{\otimes n}|v_{u^{ms}}\rangle$. After the controlled correction the output is within error $\varepsilon$ of $|\Phi_M\rangle\!\langle\Phi_M|\otimes\theta^{B'E^n}$ for some normalized $\theta$, where $|\Phi_M\rangle=M^{-1/2}\sum_m|mm\rangle$.
--
--   Thus private coding admits a coherent implementation generating EPR pairs without side communication. All construction data are existentially selected; universal performance of arbitrary codes is not claimed.
-- source:
--   Relating quantum privacy and quantum coherence: an operational approach, arXiv:quant-ph/0307053v1, PDF p. 3, Entanglement generation (4.), equations (3)–(5)

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P46

noncomputable section

namespace QAlgorithms.Papers.Independent.Next46.P46

open QAlgorithms

open scoped Matrix ComplexConjugate

attribute [local instance] Classical.decEq Classical.propDecidable

-- The repair request explicitly authorizes imports from the pinned accepted papers.

open QAlgorithms.Papers.Independent.Information100.P21 (Vec Op)

open QAlgorithms.Papers.Independent.Information100.P56 (IsLaw)

open QAlgorithms.Papers.Independent.Information100.P27 (shannon)

open QAlgorithms.Papers.Independent.Information100.P22 (bell)

open QAlgorithms.Papers.Independent.Dependency50.P21 (marginalAB)

open QAlgorithms.Papers.Independent.Frontier30.P12
  (coherentInfo quantumMutualInfo mutualAE marginalAE triCopies EntProtocol RectangularKrausData)

open QAlgorithms.Papers.Independent.Dependency50.P19 (channelSource)

open QAlgorithms.Papers.Independent.Dependency50.P48 (IsDilation)

/-- arXiv:quant-ph/0307053v1, PDF p.3, (3)--(5), scenario 4.
The input eigenvectors, codebook, phases, decoding ancilla and corrections are
chosen as part of the construction. This asserts existence, never universal
performance of every HSW/PA code or every coherent implementation. -/
theorem entanglementGeneration {X P B E : Type}
    [Fintype X] [Fintype P] [Fintype B] [Fintype E]
    [Nonempty X] [Nonempty P] [Nonempty B] [Nonempty E]
    (U : Matrix (B × E) P ℂ) (hU : IsDilation U)
    (p : X → ℝ) (hp : IsLaw p) (v : X → Vec P) (hv : Orthonormal ℂ v) :
    let psi := WithLp.toLp 2 (fun z : X × P => (Real.sqrt (p z.1) : ℂ) * v z.1 z.2)
    let rate := coherentInfo (marginalAB (pureDensity (channelSource U psi)))
    ∀ eps > (0 : ℝ), ∀ delta > (0 : ℝ), ∃ n0 : ℕ, 0 < n0 ∧
      ∀ n ≥ n0, ∃ C : CoherentGenerationData X P B n,
        C.Valid ∧ (C.uncorrected v).Valid ∧
        traceNorm (pureDensity (show
          Vec ((Fin C.m × Fin C.m) × (Fin (C.s * C.r) × (Fin n → E)))
          from (C.uncorrected v).outputVector U) -
          pureDensity (C.idealDecoded v U)) ≤ eps ∧
        (C.corrected v).Good U eps ∧
        rate - delta ≤ Real.logb 2 (C.m : ℝ) / n := by sorry

end QAlgorithms.Papers.Independent.Next46.P46

end
