-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P48_theorem_2
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P48.theorem_2
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T05:32:20.422028+00:00
-- url     : https://prove2.me/theorems/bcbfe451-805e-488b-98f6-514e82e35019
-- title:
--   Some genuinely quantum boxes are strictly parity-distillable
-- statement:
--   For real parameters $\varepsilon,\delta$, define $P_{\varepsilon,\delta}$ as follows. At a binary input pair $xy$, put $r=\varepsilon$ if $xy=11$, and $r=\delta$ otherwise. Each equal-output pair has probability $(1-r)/2$ and each unequal-output pair has probability $r/2$. These tables have uniform marginals. Let $\operatorname{NDP}_n$ apply the same local input to $n$ independent identical resource copies and return separate local XORs; let $\operatorname{NL}$ be the full absolute CHSH maximum.
--
--   There exist parameters and a copy number satisfying
--
--   $$
--   0<\delta<\varepsilon<\tfrac12,\qquad n>1,
--   $$
--
--   such that the whole table $P_{\varepsilon,\delta}$ is quantum-realizable and the local-XOR output is a valid non-signaling behavior with
--
--   $$
--   \operatorname{NL}\bigl(\operatorname{NDP}_n(P_{\varepsilon,\delta})\bigr)>
--   \operatorname{NL}(P_{\varepsilon,\delta})>2.
--   $$
--
--   Quantum realizability means exact local-measurement probabilities on a normalized bipartite state, including the uniform marginals. This establishes distillation within the quantum set, with existence rather than universality over all quantum boxes.
-- source:
--   Distilling Non-Locality, arXiv:0809.3173v4, PDF p. 3, Theorem 2: a quantum box is strictly distillable

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P48

namespace QAlgorithms.Papers.Independent.Intakethird100.P48

open scoped BigOperators TensorProduct

noncomputable section

/-- PDF p.3, Theorem 2: some 0<delta<epsilon<1/2 quantum resource is strictly
distilled by NDP_n for some n>1. Quantum refers to the entire behavior. -/
theorem theorem_2 :
    ∃ (epsilon delta : ℝ) (n : ℕ),
      0 < delta ∧ delta < epsilon ∧ epsilon < 1 / 2 ∧ 1 < n ∧
      IsQuantum (parameterBox epsilon delta) ∧
      StrictlyDistills (parityProtocol n) (parameterBox epsilon delta) := by sorry

end

end QAlgorithms.Papers.Independent.Intakethird100.P48
