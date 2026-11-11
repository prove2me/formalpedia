-- Prove2me | Theorems.Thm_QuantumAdviceAmplification_Separation_theorem_4_1
-- name    : QuantumAdviceAmplification.Separation.theorem_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T06:04:54.505876+00:00
-- url     : https://prove2.me/theorems/9fc57fe2-35d6-4bfb-b7cc-16868ae29615
-- title:
--   Theorem 4.1 — Information-theoretic quantum-advice exclusion
-- statement:
--   Let positive functions $m,k$ satisfy $k(n)\le2^n$, and let $\varepsilon(n)\in[0,1/2]$. If
--   $$m(n)<(1-H(\varepsilon(n)))k(n)$$
--   for infinitely many positive $n$, there is a single arbitrary Boolean function $R$ such that $L_R^{(k)}$ lies outside every $\mathsf{BQTIME}(t)_\varepsilon/q_m$, for every positive time function $t$, and in particular outside $\mathsf{BQP}_\varepsilon/q_m$.
--
--   The same $R$ excludes all finite-description uniform algorithms, without any effective-preparation or computability condition on the functions.
--
--   Differences from the source:
--   - encoding: N={1,2,...}, languages on finite binary strings, and positive resource functions → PNat lengths, Boolean functions on List Bool, and explicit positivity guards on natural resource values; reason: preserves every positive-length instance; empty-word values impose no correctness condition
--   - encoding: Definitions 2.5–2.6: finite-description tape machines and a fixed finite universal quantum gate set → finite transition tables on one-sided tapes, with reserved index and output work tapes; a fixed GateAlphabet and a complete self-delimiting binary circuit serialization; reason: specifies ordinary machine and encoding conventions; execution determines time and error, and the supplied binary m(n) is not computed
--   - encoding: infinitely many good lengths → for every threshold N, a good n>=N exists; reason: unboundedness of a subset of positive naturals is equivalent to infinitude
-- source:
--   Shih-Han Hung, Han-Hsuan Lin, STOC 2027 submission #1297 (October 2026), p.14, Theorem 4.1

import Definitions.Def_QuantumAdviceAmplification_Separation_parameters
set_option autoImplicit false
open Classical

namespace QuantumAdviceAmplification.Separation

theorem theorem_4_1 (G : GateAlphabet) (m k : Length → ℕ) (ε : Length → ℝ)
    (hm : ∀ n, 0 < m n) (hk : ∀ n, 0 < k n ∧ k n ≤ 2 ^ n.val)
    (hε : ∀ n, 0 ≤ ε n ∧ ε n ≤ 1 / 2)
    (hinf : InfinitelyOften (fun n => (m n : ℝ) < (1 - H (ε n)) * k n)) :
    ∃ R : Language, (∀ t : Length → ℕ, (∀ n, 0 < t n) →
      restrictedLanguage k R ∉ BQTIME G t m ε) ∧
      restrictedLanguage k R ∉ BQPAdvice G m ε := by sorry

end QuantumAdviceAmplification.Separation
