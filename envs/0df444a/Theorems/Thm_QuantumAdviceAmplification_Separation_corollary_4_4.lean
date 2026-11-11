-- Prove2me | Theorems.Thm_QuantumAdviceAmplification_Separation_corollary_4_4
-- name    : QuantumAdviceAmplification.Separation.corollary_4_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T06:04:55.802664+00:00
-- url     : https://prove2.me/theorems/63488a3a-3da4-4744-a50d-9b16a5af52b7
-- title:
--   Corollary 4.4 — Polynomial-time specialization
-- statement:
--   In the setting and with the same gap formula of Corollary 4.3, assume also that $s$ is polynomially bounded. Then
--   $$\mathsf P_{\varepsilon+\delta}/r_m\not\subseteq\mathsf{BQP}_\varepsilon/q_m.$$
--   The infinitely-many-good-lengths condition is unchanged. This passes from the full time-class separation to polynomial time without modifying the advice length or the gap.
--
--   Differences from the source:
--   - encoding: N={1,2,...}, languages on finite binary strings, and positive resource functions → PNat lengths, Boolean functions on List Bool, and explicit positivity guards on natural resource values; reason: preserves every positive-length instance; empty-word values impose no correctness condition
--   - encoding: Definitions 2.5–2.6: finite-description tape machines and a fixed finite universal quantum gate set → finite transition tables on one-sided tapes, with reserved index and output work tapes; a fixed GateAlphabet and a complete self-delimiting binary circuit serialization; reason: specifies ordinary machine and encoding conventions; execution determines time and error, and the supplied binary m(n) is not computed
--   - encoding: the constants of Theorem 4.2 → existential c1,C with the complete UpperBoundConstants property included in the conclusion; reason: ties the constants to the upper bound without assuming a proof fact or selecting a witness from an open theorem inside a definition
--   - encoding: s(n)<=n^O(1) → one eventual polynomial coefficient, exponent and threshold; reason: equivalent asymptotic statement, including arbitrary finite initial lengths
-- source:
--   Shih-Han Hung, Han-Hsuan Lin, STOC 2027 submission #1297 (October 2026), p.17, Corollary 4.4

import Definitions.Def_QuantumAdviceAmplification_Separation_parameters
set_option autoImplicit false
open Classical

namespace QuantumAdviceAmplification.Separation

theorem corollary_4_4 :
    ∃ c1 C : ℝ, UpperBoundConstants c1 C ∧
    ∀ (G : GateAlphabet) (m s : Length → ℕ) (ε : Length → ℝ),
      (∀ n, 0 < m n ∧ 0 < s n) → (∀ n, 0 ≤ ε n ∧ ε n < 1 / 2) →
      InfinitelyOften (Good c1 m s ε) → PolyBounded s →
      ¬ PAdvice m (fun n => ε n + separationDelta c1 C m s ε n) ⊆ BQPAdvice G m ε := by sorry

end QuantumAdviceAmplification.Separation
