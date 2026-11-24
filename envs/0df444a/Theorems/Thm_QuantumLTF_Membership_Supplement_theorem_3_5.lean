-- Prove2me | Theorems.Thm_QuantumLTF_Membership_Supplement_theorem_3_5
-- name    : QuantumLTF.Membership.Supplement.theorem_3_5
-- status  : Proved
-- author  : @iris
-- created : 2026-11-16T10:42:34.26025+00:00
-- url     : https://prove2.me/theorems/8c900c38-5865-433b-bfb3-98c8721639ff
-- title:
--   Theorem 3.5 — quantum membership-query lower bound $\Omega(\log(n/\epsilon))$
-- statement:
--   There are universal constants $\epsilon_0>0$ and $c>0$ such that the following holds for every $n\ge2$ and $0<\epsilon\le\epsilon_0$. Let $L$ be any quantum membership-query learner making $T$ queries. Suppose that for every unit vector $w\in\mathbb S^{n-1}$, $L$ outputs a classical hypothesis $h$ with
--   $$d_{\gamma_n}(h,f_w)\le\epsilon$$
--   with probability at least $2/3$, where $f_w(x)=\mathrm{sign}(\langle w,x\rangle)$. Then
--   $$T\ge c\log\frac n\epsilon .$$
--   The learner may be adaptive, make superposition queries at arbitrary real points, use any workspace, and output improper hypotheses (an $h$ that is not an LTF).
--
--   The bound matches the $O(\log(n/\epsilon))$ upper bound of Theorem 3.4 for homogeneous LTFs, so the query complexity of the goal theorem is optimal.
--
--   **Formalization Note** The learner model is `QMemLearner` ($\ell^2$ over real query points, an arbitrary workspace and an arbitrary final POVM); $\log$ is natural.
--
--   Differences from the source:
--   - reading: any quantum learner (adaptive, superposition queries at arbitrary real points, improper output) → QMemLearner: unit initial vector in ℓ²((ℝⁿ × {0,1}) × Ω) with Ω an arbitrary type, T calls of the bit oracle O_f, arbitrary unitaries between calls, final POVM over a measurable outcome space, arbitrary hypothesis per outcome; reason: the general learner of §3.2 written as a state-space model
--   - generalization: membership queries → bit-oracle calls that may each be controlled by a workspace predicate; reason: more learners; uncontrolled calls are the constant-true predicate, so the source's learners are included
--   - generalization: classical hypothesis h : ℝⁿ → {−1, +1} → any h : ℝⁿ → ℤ; reason: more learners; a value outside {±1} only adds disagreement, so a lower bound for these learners implies the source's
--   - reading: outputs an ε-good hypothesis with probability at least 2/3 → some measurable set of outcomes, all giving an ε-good hypothesis, has probability at least 2/3; reason: the set of good outcomes of an arbitrary hypothesis map need not be measurable
--   - encoding: Ω(log(n/ϵ)), universal ϵ0 → ∃ ε0 > 0, ∃ c > 0 before n and ε: c · log(n/ε) ≤ T; reason: the paper's O-convention; log natural
-- source:
--   Krivcenko, Nguyen, de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, arXiv:2609.40331, Theorem 3.5, Eq. (100), p. 38 (PDF p. 39); also Theorem 1.2, p. 7 (PDF p. 8)

import Mathlib
import Definitions.Def_QuantumLTF_Membership_Supplement_QMemLearner

namespace QuantumLTF.Membership.Supplement

/-- **Theorem 3.5 (Quantum membership-query lower bound).** Krivcenko, Nguyen, de Wolf, *Fast Quantum Algorithms for Learning Linear Threshold Functions*,
arXiv:2609.40331, Theorem 3.5, p. 38 (PDF p. 39),
also Theorem 1.2: "There is a universal constant `ϵ0 > 0` such that, for every `n ≥ 2` and
`0 < ϵ ≤ ϵ0`, any quantum learner that, for every `w ∈ S^{n−1}`, outputs a classical hypothesis `h`
with `d_{γn}(h, f_w) ≤ ϵ` with probability at least `2/3` requires `Ω(log(n/ϵ))` membership queries.
This holds even for adaptive algorithms making superposition queries at arbitrary real points and
outputting improper hypotheses."

**Formalization Note.** `f_w = ltf w 0`. `Ω(·)` is a constant `c > 0` chosen with `ϵ0` before `n, ϵ`.
The learner (`QMemLearner`) queries `O_f` at arbitrary real points in superposition (`ℓ²(ℝⁿ × {0,1} × Ω)`
with an arbitrary workspace `Ω`), controlled calls allowed, arbitrary unitaries between calls, an
arbitrary POVM at the end and arbitrary (improper) hypotheses. Success is read on a measurable event of
outcomes (`QMemLearner.Succeeds`). `log` is the natural logarithm. -/
theorem theorem_3_5 :
    ∃ ε0 : ℝ, 0 < ε0 ∧ ∃ c : ℝ, 0 < c ∧
      ∀ n : ℕ, 2 ≤ n → ∀ ε : ℝ, 0 < ε → ε ≤ ε0 →
        ∀ L : QMemLearner n,
          (∀ w : EuclideanSpace ℝ (Fin n), ‖w‖ = 1 → L.Succeeds w ε) →
            c * Real.log (n / ε) ≤ L.T := by sorry

end QuantumLTF.Membership.Supplement
