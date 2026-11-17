-- Prove2me | Theorems.Thm_QCollLB_Supplement_theorem_1_3
-- name    : QCollLB.Supplement.theorem_1_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T10:11:26.61152+00:00
-- url     : https://prove2.me/theorems/38cf3a19-000d-46bd-ad52-ba4e33c4b799
-- title:
--   Theorem 1.3 — one-round $k$-to-one Testing with bias $\varepsilon$ needs $t\ge(\varepsilon/6)\sqrt{n/k}$ parallel queries
-- statement:
--   Fix $k\ge2$ and $N\ge0$, let $n=kN$ (so $k\mid n$), let $q\ge n$ and $0<\varepsilon<1/2$. In **$k$-to-one Testing** an algorithm is given oracle access to $x\in\mathbb Z_q^n$, promised to be either **one-to-one** (pairwise distinct entries) or **$k$-to-one** (every value appearing in $x$ appears exactly $k$ times), and must output a bit: $0$ for one-to-one, $1$ for $k$-to-one.
--
--   A **one-round $t$-query algorithm** with workspace $W$ applies an input-independent unitary $U_0$ to an input-independent start state, one layer of $t$ parallel phase queries $O_x^{\otimes t}$ to the same input $x$, an input-independent unitary $U_1$, and a final measurement.
--
--   **Theorem.** If such an algorithm outputs $0$ with probability at least $1/2+\varepsilon$ on every one-to-one $x\in\mathbb Z_q^n$, and outputs $1$ with probability at least $1/2+\varepsilon$ on every $k$-to-one $x\in\mathbb Z_q^n$, then
--
--   $$
--   t\;\ge\;\frac{\varepsilon}{6}\sqrt{\frac nk}.
--   $$
--
--   The constant is absolute: it depends on none of $k$, $n$, $q$, $\varepsilon$ and the workspace. For $k=2$ this settles the non-adaptive collision question of Koiran, Landes, Portier and Yao, and it matches classical birthday sampling, which distinguishes the two cases with constant bias using $O(\sqrt{n/k})$ positions. The alphabet may be as small as $q=n$, the least size for which one-to-one inputs exist.
--
--   **Formalization Note** The algorithm is the published `QCollLB.OneRoundAlg` with the shared parallel phase oracle `QCollLB.parPhaseOracle`; output probabilities are `QCollLB.Supplement.testProb`, a computational-basis measurement followed by an arbitrary output map to `Fin 2`. One-to-one is `Function.Injective x`; $k$-to-one is `MultiCollQ.exactTypeSet (k*N) q k (pureType k N)`.
--
--   Differences from the source:
--   - generalization: Ω(ε√(n/k)) with an absolute constant → the explicit bound ε/6·√(n/k) ≤ t for every n, with no threshold; reason: the proof (p.64) concludes "t ≥ (ε/6)√(n/k) in all cases, with a constant independent of k"; the explicit bound specializes to the Ω statement with c = 1/6
--   - encoding: k | n → n = k·N; reason: same instances
--   - encoding: final PVM on A with outcome ρ ∈ {0, 1} → computational-basis measurement followed by an output map to Fin 2; reason: an arbitrary U_1 and workspace rotate any two-outcome PVM to the computational basis, same class
--   - encoding: q ≥ n → q ≥ n with [NeZero q]; reason: excludes only q = 0, which is not an alphabet (and is already excluded by q ≥ n once n ≥ 1)
-- source:
--   Peng–Wu, Quantum Lower Bounds for Collision Problems, arXiv:2611.01767 (PDF sha256 4e5aba34…d9fc), Theorem 1.3, p.63 (also stated p.3; proof pp.63–64, explicit constant p.64); Definition 2.1 p.15; Eq. (6) p.15

import Mathlib
import Definitions.Def_QCollLB_OneRound
import Definitions.Def_QCollLB_Supplement_testProb
import Definitions.Def_MultiCollQ_HasExactType

set_option autoImplicit false

namespace QCollLB.Supplement

/-- **Theorem 1.3 (Non-adaptive `k`-to-one Testing)** (Peng–Wu, *Quantum Lower Bounds for Collision
Problems*, arXiv:2611.01767 (PDF sha256 4e5aba34…d9fc), Theorem 1.3, p.63; also stated on p.3; proof
pp.63–64). Let `k ≥ 2` be fixed, `k | n`, `q ≥ n`, and `0 < ε < 1/2`. Every one-round quantum algorithm
for `k`-to-one Testing that succeeds with probability at least `1/2 + ε` on every promised input in
`Z_q^n` requires `Ω(ε √(n/k))` parallel queries.

**Formalization Note.** `n = kN` encodes `k | n`. The algorithm is the published one-round model
`QCollLB.OneRoundAlg (k*N) q t w` with the `t`-fold phase oracle on one shared input (Eq. (6), p.15),
for every workspace size `w`, and an arbitrary output map to a bit (`0` = one-to-one, `1` =
`k`-to-one, p.63). "Succeeds with probability at least `1/2 + ε` on every promised input" is: the
probability of outputting `0` is `≥ 1/2 + ε` on every one-to-one `x` (pairwise distinct entries,
`Function.Injective x`) and the probability of outputting `1` is `≥ 1/2 + ε` on every exactly
`k`-to-one `x` (`MultiCollQ.exactTypeSet (k*N) q k (pureType k N)`, §2.5, p.14). The `Ω` has an
absolute constant (no subscript; p.64: "with a constant independent of `k`"), made explicit as the
`1/6` the proof gives (p.64: "Thus `t ≥ (ε/6)√(n/k)` in all cases"); the bound holds for every `n`,
with no threshold. `[NeZero q]` excludes only `q = 0`. -/
theorem theorem_1_3 (k : ℕ) (hk : 2 ≤ k) (N q : ℕ) [NeZero q] (hq : k * N ≤ q) (ε : ℝ)
    (hε : 0 < ε) (hε' : ε < 1 / 2) (w t : ℕ) (A : OneRoundAlg (k * N) q t w)
    (out : ((Fin t → Fin (k * N)) × (Fin t → ZMod q)) × Fin w → Fin 2)
    (hinj : ∀ x : Fin (k * N) → ZMod q, Function.Injective x → 1 / 2 + ε ≤ testProb A out 0 x)
    (hkto1 : ∀ x ∈ MultiCollQ.exactTypeSet (k * N) q k (MultiCollQ.pureType k N),
      1 / 2 + ε ≤ testProb A out 1 x) :
    ε / 6 * Real.sqrt (((k * N : ℕ) : ℝ) / k) ≤ t := by sorry

end QCollLB.Supplement
