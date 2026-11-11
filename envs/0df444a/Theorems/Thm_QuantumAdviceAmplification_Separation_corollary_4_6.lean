-- Prove2me | Theorems.Thm_QuantumAdviceAmplification_Separation_corollary_4_6
-- name    : QuantumAdviceAmplification.Separation.corollary_4_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T06:04:55.219577+00:00
-- url     : https://prove2.me/theorems/267436ca-1132-4d1e-8039-de82708486e8
-- title:
--   Corollary 4.6 — Vanishing-gap separation at fixed advice length
-- statement:
--   There is an absolute constant $c^*>0$. Let $m$ be positive, polynomially bounded, and diverge to infinity. Let $0\le\varepsilon(n)<1/2$ with $1/2-\varepsilon(n)\ge n^{-b}$ eventually for some constant $b$. There is one function $\delta(n)\in(0,1/2]$ such that, eventually,
--   $$\delta(n)\le c^*\min\left\{\left(\frac{\log_2m(n)}{m(n)}\right)^{1/4},\frac{\sqrt{\log_2m(n)/m(n)}}{1/2-\varepsilon(n)}\right\},$$
--   and both
--   $$\mathsf P_{\varepsilon+\delta}/r_m\not\subseteq\mathsf{BQP}_\varepsilon/q_m,\qquad\mathsf{BQP}_\varepsilon/q_m\subsetneq\mathsf{BQP}_{\varepsilon+\delta}/q_m.$$
--   Uniformly in $\varepsilon$, the same gap is $O((\log_2m/m)^{1/4})$. For each fixed $\varepsilon\in(0,1/2)$ it is $O_\varepsilon(\sqrt{\log_2m/m})$ and $\varepsilon+\delta(n)<1/2$ eventually. The coefficient $c^*/(1/2-\varepsilon)$ is independent of $m$ and $n$.
--
--   This is the paper's full failure of size-preserving quantum-advice amplification, witnessed by randomized classical advice. Correctness in both classes holds at every positive length; only the numerical gap bound is eventual.
--
--   Differences from the source:
--   - encoding: N={1,2,...}, languages on finite binary strings, and positive resource functions → PNat lengths, Boolean functions on List Bool, and explicit positivity guards on natural resource values; reason: preserves every positive-length instance; empty-word values impose no correctness condition
--   - encoding: Definitions 2.5–2.6: finite-description tape machines and a fixed finite universal quantum gate set → finite transition tables on one-sided tapes, with reserved index and output work tapes; a fixed GateAlphabet and a complete self-delimiting binary circuit serialization; reason: specifies ordinary machine and encoding conventions; execution determines time and error, and the supplied binary m(n) is not computed
--   - encoding: the constants of Theorem 4.2 → existential c1,C with the complete UpperBoundConstants property included in the conclusion; reason: ties the constants to the upper bound without assuming a proof fact or selecting a witness from an open theorem inside a definition
--   - encoding: the existence and quantitative guarantees for delta → delta is explicitly the proof choice from (59),(65), cstar is the value in (67), and the fixed-error coefficient is cstar/(1/2-e); reason: exposes the witnesses supplied by the proof; cstar precedes all input data and the fixed-error coefficient is independent of m,n
-- source:
--   Shih-Han Hung, Han-Hsuan Lin, STOC 2027 submission #1297 (October 2026), p.18, Corollary 4.6 (proof pp.18–19)

import Definitions.Def_QuantumAdviceAmplification_Separation_parameters
set_option autoImplicit false
open Classical

namespace QuantumAdviceAmplification.Separation

theorem corollary_4_6 :
    ∃ c1 C cstar : ℝ, UpperBoundConstants c1 C ∧
      cstar = (2 * C + 1) * max (κ * Real.sqrt 6) (6 * κ ^ 2) ∧ 0 < cstar ∧
      ∀ (G : GateAlphabet) (m : Length → ℕ) (ε : Length → ℝ),
      (∀ n, 0 < m n) → PolyBounded m → Diverges m →
      (∀ n, 0 ≤ ε n ∧ ε n < 1 / 2) → InvPolyGap ε →
      ∃ δ : Length → ℝ,
        δ = separationDelta c1 C m (balancedBudget c1 m ε) ε ∧
        (∀ n, 0 < δ n ∧ δ n ≤ 1 / 2) ∧
        Eventually (fun n => δ n ≤ cstar *
          min (fourthRootRate (m n)) (squareRootRate (m n) / (1 / 2 - ε n))) ∧
        FullSeparation G m ε δ ∧
        Eventually (fun n => δ n ≤ cstar * fourthRootRate (m n)) ∧
        (∀ e : ℝ, 0 < e → e < 1 / 2 → (∀ n, ε n = e) →
          Eventually (fun n => δ n ≤ (cstar / (1 / 2 - e)) * squareRootRate (m n)) ∧
          Eventually (fun n => ε n + δ n < 1 / 2)) := by sorry

end QuantumAdviceAmplification.Separation
