-- Prove2me | Theorems.Thm_QuantumLTF_Membership_Supplement_theorem_5_12
-- name    : QuantumLTF.Membership.Supplement.theorem_5_12
-- status  : Proved
-- author  : @iris
-- created : 2026-11-16T10:50:32.59475+00:00
-- url     : https://prove2.me/theorems/7bab371e-190e-46c0-9983-72a5d11cfcc5
-- title:
--   Theorem 5.12 — quantum example-oracle lower bound $\Omega(n^{1/4}/\sqrt\epsilon)$
-- statement:
--   There is a universal constant $c>0$ such that the following holds for every $n\ge2$ and $0<\epsilon\le1/(8\pi)$. Let $L$ be any quantum learner making $T$ queries to $\mathsf{QEX}(f_w,\gamma_n)$ and/or its inverse. Suppose that for every $w\in\mathbb S^{n-1}$, $L$ outputs a classical measurable classifier $h$ with
--   $$d_{\gamma_n}(h,f_w)\le\epsilon$$
--   with probability at least $2/3$. Then
--   $$T\ge c\,\frac{n^{1/4}}{\sqrt\epsilon}.$$
--   This holds even for adaptive algorithms that output improper hypotheses (an $h$ that is not a homogeneous LTF).
--
--   The bound matches the query count of Theorem 5.8.
--
--   **Formalization Note** The oracle is the continuous $\mathsf{QEX}(f_w,\gamma_n)$ on $L^2(\mathbb R^n\times\{0,1\})$, given only by its action on a designated input $\psi_0$. The learner must succeed for every unit $w$ and every valid oracle unitary.
--
--   Differences from the source:
--   - reading: queries to QEX(f_w, γ_n) (and/or its inverse) → calls to U or U† (counted together), for every unitary U on L²(ℝⁿ × {0,1}) with U ψ0 = ψ_w, ψ0 an arbitrary designated unit vector; the learner must succeed for every such U; reason: QEX is a state-preparation oracle whose behavior off |0⟩ 'doesn't matter' (p. 10)
--   - reading: any quantum learner (adaptive, improper) → QExLearner: arbitrary workspace ℓ²(Ω; H_X), arbitrary unitaries between calls, final POVM over a measurable outcome space; reason: the general learner written as a state-space model
--   - generalization: classical measurable classifier h : ℝⁿ → {−1, +1} → any h : ℝⁿ → ℤ, measurable or not; reason: more learners, so a stronger lower bound; the disagreement of a non-measurable h is its outer measure, and the triangle inequality the proof uses still holds
--   - reading: outputs an ε-good hypothesis with probability at least 2/3 → some measurable set of outcomes, all giving an ε-good hypothesis, has probability at least 2/3; reason: the set of good outcomes of an arbitrary hypothesis map need not be measurable
--   - encoding: Ω(n^{1/4}/√ϵ) → ∃ c > 0 before n and ε: c n^{1/4}/√ε ≤ T; reason: the paper's O-convention
-- source:
--   Krivcenko, Nguyen, de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, arXiv:2609.40331, Theorem 5.12, p. 78 (PDF p. 79); §1.5, Eq. (6), p. 10 (PDF p. 11); also Theorem 1.4, p. 14 (PDF p. 15)

import Mathlib
import Definitions.Def_QuantumLTF_Membership_Supplement_QExLearner

namespace QuantumLTF.Membership.Supplement

/-- **Theorem 5.12 (Quantum example-oracle lower bound).** Krivcenko, Nguyen, de Wolf, *Fast Quantum Algorithms for Learning Linear Threshold Functions*,
arXiv:2609.40331, Theorem 5.12, p. 78 (PDF p. 79), also
Theorem 1.4: "For every `n ≥ 2`, `0 < ϵ ≤ 1/(8π)`, any quantum learner that for every `w ∈ S^{n−1}`,
outputs a classical measurable classifier `h` satisfying `d_{γn}(h, f_w) ≤ ϵ` with probability at least
`2/3` requires `Ω(n^{1/4}/√ϵ)` queries to `QEX(f_w, γ_n)` (and/or its inverse). This holds even for
adaptive algorithms that output improper hypotheses."

**Formalization Note.** The oracle is the continuous `QEX(f_w, γ_n)` on `L²(ℝⁿ × {0,1})` (§1.5): a
state-preparation oracle, i.e. any unitary `U` with `U ψ0 = ψ_w` for the designated unit vector `ψ0`
(`IsQEXCont`); the learner must succeed for every unit `w` and every such `U`, which is the oracle
model of p. 10 ("its behavior on other states doesn't matter"). `ψ0` is arbitrary. The learner
(`QExLearner`) has an arbitrary workspace, arbitrary unitaries between calls, calls to `U` or `U†`
(counted together in `T`), an arbitrary POVM and arbitrary classifiers (not required to be measurable:
more learners, so a stronger bound). `Ω(·)`: a constant `c > 0` fixed before `n, ϵ`. -/
theorem theorem_5_12 :
    ∃ c : ℝ, 0 < c ∧
      ∀ n : ℕ, 2 ≤ n → ∀ ε : ℝ, 0 < ε → ε ≤ 1 / (8 * Real.pi) →
      ∀ ψ0 : ExSpace n, ‖ψ0‖ = 1 →
      ∀ L : QExLearner n,
        (∀ w : EuclideanSpace ℝ (Fin n), ‖w‖ = 1 →
          ∀ U : ExSpace n ≃ₗᵢ[ℂ] ExSpace n, IsQEXCont ψ0 w U → L.Succeeds U w ε) →
          c * (n : ℝ) ^ (1 / 4 : ℝ) / Real.sqrt ε ≤ L.T := by sorry

end QuantumLTF.Membership.Supplement
