-- Prove2me | Theorems.Thm_QuantumAdviceAmplification_Separation_corollary_4_3
-- name    : QuantumAdviceAmplification.Separation.corollary_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T06:05:30.136897+00:00
-- url     : https://prove2.me/theorems/ddf1bc75-6082-493a-a72a-9327e8600a47
-- title:
--   Corollary 4.3 — General advice-error separation
-- statement:
--   Use the absolute upper-bound constants $c_1,C$ of Theorem 4.2. For positive $m,s$ and $\varepsilon(n)\in[0,1/2)$, set
--   $$k(n)=\min\{\lfloor m(n)/(1-H(\varepsilon(n)))\rfloor+1,2^n\},\qquad\eta(n)=\log_2s(n)/s(n)+s(n)/k(n).$$
--   A length is good when $m(n)<(1-H(\varepsilon(n)))2^n$ and $s(n)\ge c_1\log_2^2(2k(n))$. Set $\delta(n)=\min\{1/2,(2C+1)\Phi(\varepsilon(n),\eta(n)+1/m(n))\}$ at good lengths and $\delta(n)=1/2$ otherwise. If good lengths occur infinitely often, then $0<\delta(n)\le1/2$ at every length and
--   $$\mathsf{DTIME}(n^2+s)_{\varepsilon+\delta}/r_m\not\subseteq\mathsf{BQP}_\varepsilon/q_m.$$
--   This retains the full time-class separation and both branches of the gap definition.
--
--   Differences from the source:
--   - encoding: N={1,2,...}, languages on finite binary strings, and positive resource functions → PNat lengths, Boolean functions on List Bool, and explicit positivity guards on natural resource values; reason: preserves every positive-length instance; empty-word values impose no correctness condition
--   - encoding: Definitions 2.5–2.6: finite-description tape machines and a fixed finite universal quantum gate set → finite transition tables on one-sided tapes, with reserved index and output work tapes; a fixed GateAlphabet and a complete self-delimiting binary circuit serialization; reason: specifies ordinary machine and encoding conventions; execution determines time and error, and the supplied binary m(n) is not computed
--   - encoding: the constants of Theorem 4.2 → existential c1,C with the complete UpperBoundConstants property included in the conclusion; reason: ties the constants to the upper bound without assuming a proof fact or selecting a witness from an open theorem inside a definition
-- source:
--   Shih-Han Hung, Han-Hsuan Lin, STOC 2027 submission #1297 (October 2026), p.17, Corollary 4.3

import Definitions.Def_QuantumAdviceAmplification_Separation_parameters
set_option autoImplicit false
open Classical

namespace QuantumAdviceAmplification.Separation

theorem corollary_4_3 :
    ∃ c1 C : ℝ, UpperBoundConstants c1 C ∧
    ∀ (G : GateAlphabet) (m s : Length → ℕ) (ε : Length → ℝ),
      (∀ n, 0 < m n ∧ 0 < s n) → (∀ n, 0 ≤ ε n ∧ ε n < 1 / 2) →
      InfinitelyOften (Good c1 m s ε) →
      (∀ n, 0 < separationDelta c1 C m s ε n ∧ separationDelta c1 C m s ε n ≤ 1 / 2) ∧
      ¬ DTIME (fun n => n.val ^ 2 + s n) m (fun n => ε n + separationDelta c1 C m s ε n) ⊆
        BQPAdvice G m ε := by sorry

end QuantumAdviceAmplification.Separation
