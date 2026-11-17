-- Prove2me | Theorems.Thm_QuantumLTF_Membership_Supplement_theorem_A_3
-- name    : QuantumLTF.Membership.Supplement.theorem_A_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T10:51:38.949231+00:00
-- url     : https://prove2.me/theorems/1c043e06-a108-411f-9358-1b32e2f940ba
-- title:
--   Theorem A.3 — classical randomized membership-query lower bound $\Omega(n\log(1/\epsilon))$
-- statement:
--   There are universal constants $\epsilon_0>0$ and $c>0$ such that the following holds for every $n\ge2$ and $0<\epsilon\le\epsilon_0$. Suppose a randomized classical membership-query learner making at most $q$ queries, for every $w\in\mathbb S^{n-1}$, outputs with probability at least $2/3$ a classifier $h$ with $d_{\gamma_n}(h,f_w)\le\epsilon$. Then
--   $$q\ge c\,n\log\frac1\epsilon .\qquad(207)$$
--
--   Compared with Theorem 3.5, quantum membership queries give an exponential improvement in $n$.
--
--   **Formalization Note** A randomized learner is a probability space of seeds and, for each seed, a deterministic adaptive query tree at arbitrary real points with any hypothesis at its leaves; $q$ bounds every tree's depth.
--
--   Differences from the source:
--   - reading: randomized classical membership-query learner → a probability space (Ω, μ) and, for each seed ω, a deterministic real-point query tree (base QueryTree) of depth ≤ q; reason: a randomized algorithm is a distribution over deterministic ones (proof of Lemma A.1)
--   - generalization: classical hypothesis h : ℝⁿ → {−1, +1} → any h : ℝⁿ → ℤ; reason: more learners; a value outside {±1} only adds disagreement, so a lower bound for these learners implies the source's
--   - reading: outputs with probability at least 2/3 a classifier with d ≤ ϵ → some measurable set of seeds, on which the output is ε-good, has probability at least 2/3; reason: the good set of an arbitrary family of trees need not be measurable
--   - encoding: ϵ0 sufficiently small universal constant; q = Ω(n log(1/ϵ)) → ∃ ε0 > 0, ∃ c > 0 before n and ε: c n log(1/ε) ≤ q; reason: the paper's O-convention; log natural
-- source:
--   Krivcenko, Nguyen, de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, arXiv:2609.40331, Theorem A.3, Eq. (207), p. 87 (PDF p. 88)

import Mathlib
import Definitions.Def_QuantumLTF_Membership_ltf
import Definitions.Def_QuantumLTF_Membership_disagree
import Definitions.Def_QuantumLTF_Membership_QueryTree

namespace QuantumLTF.Membership.Supplement

open MeasureTheory QuantumLTF.Membership

/-- **Theorem A.3 (Classical randomized MQ lower bound).** Krivcenko, Nguyen, de Wolf, *Fast Quantum Algorithms for Learning Linear Threshold Functions*,
arXiv:2609.40331, Theorem A.3, p. 87 (PDF p. 88): "Let
`n ≥ 2` and let `0 < ϵ ≤ ϵ0`, where `ϵ0 > 0` is a sufficiently small universal constant. Any randomized
classical membership-query learner that, for every `w ∈ S^{n−1}`, outputs with probability at least
`2/3` a classifier `h` satisfying `d_{γn}(h, f_w) ≤ ϵ` requires `q = Ω(n log(1/ϵ))` (207) queries."

**Formalization Note.** A randomized learner is a probability space `(Ω, μ)` of random seeds and, for
each seed `ω`, a deterministic adaptive membership-query tree `t ω` (base `QueryTree`: queries at
arbitrary real points, any hypothesis `ℝⁿ → ℤ` at the leaves, so improper hypotheses are allowed); `q`
bounds the number of queries of every tree. Success for `w` (`f_w = ltf w 0`) is read on a measurable
event: some measurable set of seeds, on which the output is `ϵ`-good, has probability `≥ 2/3`.
`ϵ0` and the constant `c` of `Ω(·)` are fixed before `n, ϵ`; `log` natural. -/
theorem theorem_A_3 :
    ∃ ε0 : ℝ, 0 < ε0 ∧ ∃ c : ℝ, 0 < c ∧
      ∀ n : ℕ, 2 ≤ n → ∀ ε : ℝ, 0 < ε → ε ≤ ε0 →
      ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (t : Ω → QueryTree n (EuclideanSpace ℝ (Fin n) → ℤ)) (q : ℕ),
        (∀ ω, (t ω).depth ≤ q) →
        (∀ w : EuclideanSpace ℝ (Fin n), ‖w‖ = 1 →
          ∃ S : Set Ω, MeasurableSet S ∧
            S ⊆ {ω | disagree ((t ω).run (ltf w 0)) (ltf w 0) ≤ ε} ∧ (2 / 3 : ENNReal) ≤ μ S) →
          c * n * Real.log (1 / ε) ≤ q := by sorry

end QuantumLTF.Membership.Supplement
