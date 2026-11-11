-- Prove2me | Theorems.Thm_QCollLB_theorem_1_2
-- name    : QCollLB.theorem_1_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T09:15:16.988578+00:00
-- url     : https://prove2.me/theorems/0028a699-6952-4853-888d-391cbb723139
-- title:
--   Theorem 1.2 — one-round Promised $k$-to-one Finding needs $\Omega_k(n^{1-1/k})$ parallel queries
-- statement:
--   Let $k\ge2$ be fixed, $n=kN$ and $q\ge N$. Every one-round quantum algorithm for Promised $k$-to-one Finding that succeeds with constant probability on every promised input in $\mathbb Z_q^n$ requires $\Omega_k(n^{1-1/k})$ parallel queries.
--
--   Precisely: for every $k\ge2$ and every $p_0>0$ there are $c>0$ and $N_0$ such that for all $N\ge N_0$, all $q\ge N$, every workspace, every one-round algorithm making $t$ parallel queries to the phase oracle of one shared input, and every output rule, if for every exactly $k$-to-one $x\in\mathbb Z_q^{kN}$ the algorithm outputs a $k$-collision of $x$ with probability at least $p_0$, then
--   $$
--   t\ \ge\ c\,(kN)^{1-1/k}.
--   $$
--
--   The bound is tight up to constants and does not depend on the alphabet size $q$.
--
--   Differences from the source:
--   - reading: "constant probability" → every fixed threshold p₀ > 0, with c and N₀ depending only on (k, p₀); reason: §2.1, p.13: asymptotics with "success thresholds fixed in advance" and constants depending on the fixed parameters; this is the strongest reading
--   - encoding: Ω_k(n^{1−1/k}) as n → ∞ → ∃ c > 0, ∃ N₀, ∀ N ≥ N₀: t ≥ c (kN)^{1−1/k}; reason: definition of Ω_k
--   - encoding: output a set S of k indices; final PVM on A → an ordered k-tuple with distinct entries; computational-basis measurement followed by an arbitrary map out; reason: with arbitrary U_1 and workspace every PVM is diagonal in a rotated computational basis
--   - encoding: k-to-one strings in Z_q^n → MultiCollQ.exactTypeSet (k*N) q k (pureType k N), with [NeZero q]; reason: on [kN], N values of multiplicity k and nothing else is exactly k-to-one; NeZero only excludes q = 0
-- source:
--   Peng–Wu, Quantum Lower Bounds for Collision Problems, arXiv:2611.01767 (PDF sha256 4e5aba34…d9fc), Theorem 1.2, p.3 (restated with proof p.56)

import Mathlib
import Definitions.Def_QCollLB_OneRound

namespace QCollLB

/-- **Theorem 1.2 (Non-adaptive Promised `k`-to-one Finding)** (Peng–Wu, *Quantum Lower Bounds for
Collision Problems*, arXiv:2611.01767 (PDF sha256 4e5aba34…d9fc), Theorem 1.2, p.3; restated with its
proof p.56). Let `k ≥ 2` be fixed, `n = kN`, and `q ≥ N`. Every one-round quantum algorithm for
Promised `k`-to-one Finding that succeeds with constant probability on every promised input in
`Z_q^n` requires `Ω_k(n^{1−1/k})` parallel queries.

**Formalization Note.** "Constant probability" is every fixed success threshold `p₀ > 0` (§2.1,
p.13: "success thresholds fixed in advance"); `Ω_k` is: there are `c > 0` and `N₀` depending only on
`k` and `p₀` such that for all `N ≥ N₀`, every alphabet size `q ≥ N`, every workspace size `w`, every
one-round algorithm with `t` parallel queries to the `t`-fold phase oracle on one shared input, and
every output map, success probability `≥ p₀` on every exactly `k`-to-one `x ∈ Z_q^{kN}` forces
`t ≥ c (kN)^{1−1/k}`. The promised inputs are `MultiCollQ.exactTypeSet (k*N) q k (pureType k N)`: on
`[kN]`, `N` values of multiplicity `k` and no other value, i.e. every value appearing in `x` appears
exactly `k` times (§2.5, p.14). `[NeZero q]` excludes only `q = 0`. -/
theorem theorem_1_2 (k : ℕ) (hk : 2 ≤ k) (p₀ : ℝ) (hp₀ : 0 < p₀) :
    ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ (q : ℕ) [NeZero q], N ≤ q →
      ∀ (w t : ℕ) (A : OneRoundAlg (k * N) q t w)
        (out : ((Fin t → Fin (k * N)) × (Fin t → ZMod q)) × Fin w → (Fin 1 → Fin k → Fin (k * N))),
        (∀ x ∈ MultiCollQ.exactTypeSet (k * N) q k (MultiCollQ.pureType k N),
          p₀ ≤ oneRoundSuccess A out x) →
        c * ((k * N : ℕ) : ℝ) ^ (1 - 1 / (k : ℝ)) ≤ t := by sorry

end QCollLB
