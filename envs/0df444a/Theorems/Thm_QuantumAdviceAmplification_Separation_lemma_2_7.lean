-- Prove2me | Theorems.Thm_QuantumAdviceAmplification_Separation_lemma_2_7
-- name    : QuantumAdviceAmplification.Separation.lemma_2_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T06:04:32.502089+00:00
-- url     : https://prove2.me/theorems/fbf31ba8-eae7-4e30-ba6a-97299d60135a
-- title:
--   Lemma 2.7 — Basic facts about advice classes
-- statement:
--   Fix positive time and advice-length functions $t,m$ and error functions $\varepsilon,\varepsilon'\in[0,1]$.
--
--   1. Pointwise $\varepsilon\le\varepsilon'$ implies both classical and quantum time-$t$ class inclusions.
--   2. If $\varepsilon\ge1/2$ pointwise, every language belongs to the classical time-$t$ class.
--   3. If $m$ is polynomially bounded, polynomial-time randomized classical advice is simulated exactly by mixed quantum advice of the same length.
--
--   $$\mathsf P_\varepsilon/r_m\subseteq\mathsf{BQP}_\varepsilon/q_m.$$
--
--   The three clauses fix monotonicity, the half-error boundary, and the relation between the two advice models.
--
--   Differences from the source:
--   - encoding: N={1,2,...}, languages on finite binary strings, and positive resource functions → PNat lengths, Boolean functions on List Bool, and explicit positivity guards on natural resource values; reason: preserves every positive-length instance; empty-word values impose no correctness condition
--   - encoding: Definitions 2.5–2.6: finite-description tape machines and a fixed finite universal quantum gate set → finite transition tables on one-sided tapes, with reserved index and output work tapes; a fixed GateAlphabet and a complete self-delimiting binary circuit serialization; reason: specifies ordinary machine and encoding conventions; execution determines time and error, and the supplied binary m(n) is not computed
--   - encoding: m(n)<=n^O(1) → one eventual natural coefficient and exponent with an explicit threshold; reason: equivalent polynomial bound, without a computability condition
-- source:
--   Shih-Han Hung, Han-Hsuan Lin, STOC 2027 submission #1297 (October 2026), p.7, Lemma 2.7

import Definitions.Def_QuantumAdviceAmplification_Separation_parameters
set_option autoImplicit false
open Classical

namespace QuantumAdviceAmplification.Separation

theorem lemma_2_7 (G : GateAlphabet) (t m : Length → ℕ) (ε ε' : Length → ℝ)
    (ht : ∀ n, 0 < t n) (hm : ∀ n, 0 < m n)
    (hε : ∀ n, 0 ≤ ε n ∧ ε n ≤ 1) (hε' : ∀ n, 0 ≤ ε' n ∧ ε' n ≤ 1) :
    ((∀ n, ε n ≤ ε' n) → DTIME t m ε ⊆ DTIME t m ε' ∧
      BQTIME G t m ε ⊆ BQTIME G t m ε') ∧
    ((∀ n, 1 / 2 ≤ ε n) → ∀ L : Language, L ∈ DTIME t m ε) ∧
    (PolyBounded m → PAdvice m ε ⊆ BQPAdvice G m ε) := by sorry

end QuantumAdviceAmplification.Separation
