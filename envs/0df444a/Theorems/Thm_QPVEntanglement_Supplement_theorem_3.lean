-- Prove2me | Theorems.Thm_QPVEntanglement_Supplement_theorem_3
-- name    : QPVEntanglement.Supplement.theorem_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T00:20:43.5676+00:00
-- url     : https://prove2.me/theorems/25753063-b8c0-41a6-bfb8-791283af1644
-- title:
--   Theorem 3 — concrete security: every coalition winning with probability $\ge(1-10^{-7})^k$ needs $\ge c\,sR_Hm/k$ qubits
-- statement:
--   This item is stated in the **operator-requested pinned-down model** of the paper's adversary model (§4, pp.28–29). The paper defines its coalitions only operationally, so the mission fixes a precise model (choices P1–P14 of the mission description) and states the paper's result in it at full strength.
--
--   Let $\nu=1-10^{-7}$. There is a universal constant $c>0$ with the following property. Let $m,s,R_H,k$ be integers with $1\le k<m$, $s\ge9$ and $R_H\ge1$. Consider the one-dimensional protocol of Figure 3 with $m$ rounds, $s$ slots per round and $R_H$ stored BB84 states, for any admissible geometry and any timing schedule. Let $\mathcal C$ be a coalition with no station at the claimed location such that
--
--   $$\Pr[\mathcal C\text{ is accepted}]\ \ge\ \nu^k .$$
--
--   Then its total quantum-register size satisfies
--
--   $$Q(\mathcal C)\ \ge\ c\,\frac{s\,R_H\,m}{k}.$$
--
--   This is the finite-parameter form of the paper's main theorem: there is no security parameter, and the bound holds for every parameter choice. Remark 3 (p.46) gives $Q>\lfloor m/k\rfloor R_H(2\kappa(s-2.5)-1)$ with $\kappa=0.09$, which yields such a $c$. Since the schedule's slot spacing is arbitrary, the guarantee holds at the resolution of any clock that distinguishes $s$ ticks per unit of time.
--
--   Differences from the source:
--   - reading: finite LOCC adversarial coalition (§4 Adversary Model, clauses 1–6, pp.28–29) → `Coalition S` with `acceptProb` and `size` of the mission's pinned model (P5–P11); reason: operator-requested pinned-down model (OPERATOR_NOTE 2026-11-11); the paper's model is not precise enough to state as written
--   - generalization: there exists a QPV protocol in 1-D, given a clock with s reliably distinguishable ticks in a unit interval → the protocol of Figure 3, for every admissible geometry and every schedule satisfying (S1)–(S3) with any slot spacing Δ > 0; reason: the protocol is the paper's own witness (Remark 3); schedules exist for every geometry and every Δ > 0 (verification file of the base mission), in particular Δ = 1/s, so the universal statement implies the existential one
--   - encoding: universal constants c, ν with c > 0, ν = 1 − 10⁻⁷ → ∃ c > 0 quantified before m, s, R_H, k and before the geometry, schedule and coalition; ν written out as 1 − 1/10⁷; reason: universality of c is the quantifier order; ν is a fixed number
--   - encoding: integer protocol parameters m, s, R_H, k with 1 ≤ k < m, s ≥ 9, R_H ≥ 1 → natural numbers with the same inequalities, the bound c·s·R_H·m/k computed in ℝ; reason: the constraints make every parameter positive; real division is exact since k ≥ 1
--   - encoding: labels 1 … R_H + m − 1, rounds and slots 1-based → 0-based labels, rounds, slots; reason: index shift
-- source:
--   Behera, Goyal, Breaking the Bounded Entanglement Barrier for Quantum Position Verification, arXiv:2609.39234 (sha256 bdf2928d…), Theorem 3, p.6; proof: Remark 3, p.46

import Mathlib
import Definitions.Def_QPVEntanglement_Coalition_size

set_option autoImplicit false

namespace QPVEntanglement.Supplement

open QPVEntanglement

/-- **Theorem 3 (Concrete Security in the discrete-time model)**, p.6, stated in the
operator-requested pinned-down model of §4 (the published model of the mission). Behera–Goyal,
*Breaking the Bounded Entanglement Barrier for Quantum Position Verification*, arXiv:2609.39234
(sha256 bdf2928d…), Theorem 3, p.6; proof: Remark 3, p.46.

There is a universal constant `c > 0` such that for all integers `m, s, R_H, k` with
`1 ≤ k < m`, `s ≥ 9`, `R_H ≥ 1`, every admissible one-dimensional geometry, every schedule of the
protocol of Figure 3 and every coalition with no station at the claimed location that is accepted
with probability at least `ν^k`, `ν = 1 − 10⁻⁷`, has total quantum-register size at least
`c·s·R_H·m/k`.

**Formalization Note.** "There exists a QPV protocol in 1-D" is witnessed by the paper's own
protocol of Figure 3 (Remark 3); "a clock with `s` reliably distinguishable ticks in a unit
interval" is covered by the quantifier over every schedule (every slot spacing `Δ > 0`, in
particular `Δ = 1/s`). Remark 3's explicit bound `Q > ⌊m/k⌋ R_H (2κ(s − 2.5) − 1)`, `κ = 0.09`,
gives for instance `c = 0.17/18`. No security parameter and no "large enough" clause: the claim
is for every finite parameter choice. Rounds, slots and labels are 0-based. -/
theorem theorem_3 :
    ∃ c : ℝ, 0 < c ∧
      ∀ m s RH k : ℕ, 1 ≤ k → k < m → 9 ≤ s → 1 ≤ RH →
        ∀ (G : Geometry) (S : Schedule G m RH s) (C : Coalition S), (∀ a, C.pos a ≠ G.x) →
          (1 - 1 / 10 ^ 7 : ℝ) ^ k ≤ C.acceptProb →
            c * (s : ℝ) * (RH : ℝ) * (m : ℝ) / (k : ℝ) ≤ (C.size : ℝ) := by sorry

end QPVEntanglement.Supplement
