-- Prove2me | Theorems.Thm_SigmoidWire_Supplement_theorem_6_10
-- name    : SigmoidWire.Supplement.theorem_6_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T11:47:08.488466+00:00
-- url     : https://prove2.me/theorems/0dd0ce66-cd38-43eb-a7b3-e65b6d8f6ec2
-- title:
--   Theorem 6.10 — for every unbounded non-decreasing depth budget $d(n)$, $\mathrm{IP2}$ has sigmoidal circuits of depth $\le d(n)$ with $o(n)$ gates
-- statement:
--   Let $d:\mathbb N\to\mathbb N$ be non-decreasing and unbounded. Then there are a constant $\varepsilon_0>0$, a threshold $N_0$ and sigmoidal circuits $S_n$ on $2n$ inputs such that for every $n\ge N_0$, $S_n$ has depth at most $d(n)$ and computes $\mathrm{IP2}$ on $n$ coordinates with separation $\varepsilon_0$, and the number of gates of $S_n$ is $o(n)$:
--   $$\frac{\#\text{gates}(S_n)}{n}\ \longrightarrow\ 0\qquad(n\to\infty).$$
--
--   Theorem 1.7 achieves $O(\sqrt n\log n)$ gates at depth about $\sqrt n\log n$; this theorem shows that any unbounded depth already suffices for a sublinear gate count.
--
--   Differences from the source:
--   - generalization: d unbounded and increasing → d non-decreasing (Monotone d) and unbounded (∀ D ∃ n, D ≤ d n); reason: a weaker hypothesis: every unbounded increasing d is such a function
--   - reading: a set of Sigmoid circuits S computing IP2 on n coordinates with depth at most d(n) → S n for every n ≥ N₀ computes IP2 with depth ≤ d n; reason: the statement is asymptotic ("the asymptotic gates … is o(n)") and the proof needs d(n) ≥ 4; a non-decreasing d may be small on an initial segment, and no circuit has depth 0 (d(0) = 0 is allowed by "increasing")
--   - generalization: computing IP2 with an unrestricted-weight Sigmoid circuit, i.e. with no separation (p.3) → with one constant separation ε₀ > 0 (ComputesSep … ε₀) for every n ≥ N₀; reason: the proof gives "a constant separation" (p.46); separation ε₀ implies no separation
--   - encoding: the asymptotic gates of S_i is o(n) → (gates of S n)/n → 0 as n → ∞; reason: definition of o(n)
-- source:
--   Li, Reichman, Williams, Wu, New Gate, Weight and Wire Complexity Bounds for Sigmoid Neural Networks, STOC 2027 submission (manuscript sha256 2d6ef7af…), Theorem 6.10, p.45

import Mathlib
import Definitions.Def_SigmoidWire_Circuit
import Definitions.Def_SigmoidWire_ComputesSep
import Definitions.Def_SigmoidWire_Supplement_ip2

namespace SigmoidWire.Supplement

open SigmoidWire Filter Topology

/-- **Theorem 6.10 (sublinear gate count for IP2 at growing depth).**

J. Li, D. Reichman, R. Williams, T. Wu, *New Gate, Weight and Wire Complexity Bounds for Sigmoid
Neural Networks*, STOC 2027 submission (manuscript sha256 2d6ef7af…), Theorem 6.10, p.45 (PDF p.47): "Theorem 6.10 (Sublinear gate for growing depth). For any
unbounded increasing d : N → N, there exists a set of Sigmoid circuits S computing IP2 on n
coordinates with depth at most d(n) such that the asymptotic gates of S_i is o(n)."

**Formalization Note.** "Increasing" is read as non-decreasing (`Monotone d`) and "unbounded" as
`∀ D, ∃ n, D ≤ d n`; this hypothesis is weaker than strict increase. The family `S n` (a circuit on
the `2n` inputs of IP2 on `n` coordinates) computes IP2 with depth at most `d n` and one constant
separation `ε₀ > 0` ("we obtain a constant separation", p.46) for every `n ≥ N₀`, and its number of
gates `(S n).size + 1` is `o(n)`: `(gates of S n)/n → 0`. The threshold `N₀` is needed because the
proof requires `d(n) ≥ 4` and a non-decreasing `d` may be small on an initial segment. -/
theorem theorem_6_10 (d : ℕ → ℕ) (hd : Monotone d) (hunb : ∀ D : ℕ, ∃ n, D ≤ d n) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ N₀ : ℕ, ∃ S : (n : ℕ) → Circuit (n + n),
      (∀ n : ℕ, N₀ ≤ n → (S n).depth ≤ d n ∧ ComputesSep Real.sigmoid (S n) (ip2 n) ε₀) ∧
      Tendsto (fun n : ℕ => (((S n).size + 1 : ℕ) : ℝ) / n) atTop (𝓝 0) := by sorry

end SigmoidWire.Supplement
