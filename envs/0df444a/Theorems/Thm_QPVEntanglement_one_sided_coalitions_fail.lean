-- Prove2me | Theorems.Thm_QPVEntanglement_one_sided_coalitions_fail
-- name    : QPVEntanglement.one_sided_coalitions_fail
-- status  : Open
-- author  : @iris
-- created : 2026-11-11T08:38:09.103249+00:00
-- url     : https://prove2.me/theorems/94dae3e9-d1b9-4f02-9caa-d21cd80acd44
-- title:
--   §7, proof of Theorem 7, p.38 — one-sided coalitions win with probability at most $((1+1/s)/2)^m$
-- statement:
--   This item is stated in the **operator-requested pinned-down model** of the paper's adversary model (§4, pp.28–29): the paper defines its coalitions only operationally, so the mission fixes a precise model (choices P1–P14 of the mission description) and states the paper's result in it at full strength.
--
--   Let a coalition have every station strictly on one side of the claimed location $x$ (all $\mathrm{pos}_a<x$, or all $\mathrm{pos}_a>x$). In every round, a challenge from the verifier on the other side cannot reach the stations and influence a response in time, so it is answered correctly with probability at most $1/s$; the other challenge is bounded by $1$. Hence, for every geometry, every schedule, every $m$, $R_H$ and every $s\ge1$,
--
--   $$\Pr[\text{accept}]\le\Big(\frac{1+1/s}{2}\Big)^m,$$
--
--   which is at most $(5/9)^m$ for $s\ge9$. This is the first step of the proof of Theorem 7: a successful coalition has stations on both sides.
--
--   Differences from the source:
--   - reading: adversarial coalition defined operationally (§4 Adversary Model, clauses 1–6, pp.28–29; protocol rules 1–5, pp.30–32) → `Coalition S`: finitely many stations at distinct positions, each with q a qubits and fixed-time events applying a view-dependent complete Kraus instrument and an absorb/launch action, causal w.r.t. the light cone; `acceptProb` and `size` as in the mission description (P5–P11); reason: operator-requested pinned-down model (OPERATOR_NOTE 2026-11-11); the paper's model is not precise enough to state as written
--   - generalization: p_win ≤ (5/9)^m, for s ≥ 9 → acceptProb ≤ ((1 + 1/s)/2)^m for every s ≥ 1; reason: the argument proves the per-round factor (1+1/s)/2, which is ≤ 5/9 exactly when s ≥ 9; the printed bound follows
--   - generalization: the protocol's concrete timing (never fixed by the paper), claimed location translated to 0 and reflected (p.36) → every admissible geometry and every schedule satisfying (S1)–(S3), any Δ > 0; reason: quantifying over all specializes to every concrete choice; carries slot-based and inter-slot-delay independence (Definition 3)
--   - reading: … < ν(λ) for all sufficiently large λ … This contradicts the theorem hypothesis → omitted; reason: the passage's last sentences use the bound inside the proof of Theorem 7 (a fact about m = ω(log₂²λ), not about coalitions); the goal theorem states the conclusion
-- source:
--   Behera, Goyal, Breaking the Bounded Entanglement Barrier for Quantum Position Verification, arXiv:2609.39234 (sha256 bdf2928d…), §7, proof of Theorem 7, "Setting up the Framework", p.38 (unnumbered)

import Mathlib
import Definitions.Def_QPVEntanglement_Coalition_acceptProb

set_option autoImplicit false

namespace QPVEntanglement

/-- **One-sided coalitions fail** (§7, proof of Theorem 7, "Setting up the Framework", p.38;
unnumbered), stated in the operator-requested pinned-down model of §4 (BRIEF P1–P14).
Behera–Goyal, arXiv:2609.39234 (sha256 bdf2928d…), §7, p.38.

If every station lies strictly on one side of the claimed location, then in every round the
challenge from the verifier on the other side is answered in time with probability at most
`1/s` and the other challenge with probability at most `1`, so the coalition is accepted with
probability at most `((1 + 1/s)/2)^m` (`≤ (5/9)^m` for `s ≥ 9`).

**Formalization Note.** Every geometry, every schedule (any `Δ > 0`), every `m, R_H` and every
`s ≥ 1`; "left"/"right" are relative to the claimed location `x`, not to `V₀`. The paper prints
the consequence `(5/9)^m` for `s ≥ 9`; the per-round factor `(1 + 1/s)/2` is what its argument
proves. -/
theorem one_sided_coalitions_fail (G : Geometry) (m RH s : ℕ) (hs : 1 ≤ s)
    (S : Schedule G m RH s) (C : Coalition S)
    (hside : (∀ a, C.pos a < G.x) ∨ (∀ a, G.x < C.pos a)) :
    C.acceptProb ≤ ((1 + 1 / (s : ℝ)) / 2) ^ m := by sorry

end QPVEntanglement
