-- Prove2me | Theorems.Thm_QCollLB_Supplement_theorem_1_1
-- name    : QCollLB.Supplement.theorem_1_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T10:10:48.649263+00:00
-- url     : https://prove2.me/theorems/2e4fc61f-c734-47c5-9791-6f817d1cc24b
-- title:
--   Theorem 1.1 — adaptive Promised $k$-to-one Finding needs $\Omega_k(n^{(2^{k-1}-1)/(2^k-1)})$ queries
-- statement:
--   Fix $k\ge 2$. For $N\ge1$ let $n=kN$ and let $q\ge N$. A string $x\in\mathbb Z_q^n$ is **$k$-to-one** if every value appearing in $x$ appears exactly $k$ times. In **Promised $k$-to-one Finding** the algorithm is given oracle access to a $k$-to-one $x$ and must output a $k$-collision: $k$ distinct positions $i_1,\dots,i_k$ with $x_{i_1}=\dots=x_{i_k}$.
--
--   A (fully adaptive) **$T$-query algorithm** with workspace $W$ starts in an input-independent unit state, alternates input-independent unitaries $U_0,\dots,U_T$ on $I\otimes C\otimes W$ with $T$ applications of the phase oracle $O_x|i,c\rangle=\omega_q^{c\,x_i}|i,c\rangle$ ($\omega_q=e^{2\pi\imath/q}$), and finally measures and outputs a tuple of positions.
--
--   **Theorem.** For every success threshold $p_0>0$ there are constants $c>0$ and $N_0$, depending only on $k$ and $p_0$, such that for every $N\ge N_0$ and every $q\ge N$: if a $T$-query algorithm outputs a $k$-collision of $x$ with probability at least $p_0$ for every $k$-to-one $x\in\mathbb Z_q^{kN}$, then
--
--   $$
--   T\;\ge\;c\,n^{\frac{2^{k-1}-1}{2^k-1}},\qquad n=kN .
--   $$
--
--   The exponent equals $\alpha_k=\tfrac12-\tfrac1{2(2^k-1)}$, the exponent of the Liu–Zhandry multicollision algorithm, so the bound shows that this algorithm is optimal under the exact $k$-to-one promise, for every alphabet size $q\ge N$. For $k=2$ it is the $n^{1/3}$ collision bound.
--
--   **Formalization Note** "Constant probability" is read as every fixed threshold $p_0>0$, with $c$ and $N_0$ chosen before $N$, $q$, the workspace, $T$, the algorithm and its output map. The algorithm is the published `QAlgorithms.QueryAlg` with the phase oracle `SelectiveDPT.phaseOracle`; success is `SelectiveDPT.successProb` for the relation `MultiCollQ.collisionRel k 1` (an ordered tuple of $k$ distinct positions with a common value). The $k$-to-one inputs are `MultiCollQ.exactTypeSet (k*N) q k (pureType k N)`. The final measurement is a computational-basis measurement followed by an arbitrary output map, which with arbitrary $U_T$ and workspace covers every projective measurement.
--
--   Differences from the source:
--   - encoding: Ω_k(n^{(2^{k−1}−1)/(2^k−1)}) with constant success probability → ∀ p₀ > 0 ∃ c > 0 ∃ N₀ (depending on k, p₀) ∀ N ≥ N₀ … c·(kN)^{(2^{k−1}−1)/(2^k−1)} ≤ T; reason: the paper's convention (§2.1, success thresholds fixed in advance; proof p.51 picks c from p₀, then N large)
--   - encoding: final PVM {Π_ρ} on A → computational-basis measurement followed by an output map; reason: an arbitrary U_T and workspace rotate any PVM to the computational basis, same class
--   - encoding: q ≥ N → q ≥ N with [NeZero q]; reason: excludes only q = 0, which q ≥ N ≥ N₀ already excludes once N ≥ 1, and Z_0 is not an alphabet
--   - encoding: a k-collision is a set S = {i_1, …, i_k} ⊆ [n] of k distinct indices with equal values, [n] = {1, …, n} → an ordered injective k-tuple of positions in Fin (k*N) (0-based) with a common value, MultiCollQ.collisionRel k 1; reason: listing a set in any order gives such a tuple and the tuple's image is such a set, so the success events coincide
-- source:
--   Peng–Wu, Quantum Lower Bounds for Collision Problems, arXiv:2611.01767 (PDF sha256 4e5aba34…d9fc), Theorem 1.1, p.50 (also stated p.2; proof p.51); Definition 2.2 p.15; Eq. (5) p.15

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Query
import Definitions.Def_SelectiveDPT_phaseOracle
import Definitions.Def_SelectiveDPT_Qrel
import Definitions.Def_MultiCollQ_HasExactType
import Definitions.Def_MultiCollQ_collisionRel

set_option autoImplicit false

namespace QCollLB.Supplement

open QAlgorithms

/-- **Theorem 1.1 (Adaptive Promised `k`-to-one Finding)** (Peng–Wu, *Quantum Lower Bounds for
Collision Problems*, arXiv:2611.01767 (PDF sha256 4e5aba34…d9fc), Theorem 1.1, p.50; also stated on
p.2; proof p.51). Let `k ≥ 2` be fixed, `n = kN`, and `q ≥ N`. Every quantum algorithm for Promised
`k`-to-one Finding that succeeds with constant probability on every promised input in `Z_q^n` requires
`Ω_k(n^{(2^{k−1}−1)/(2^k−1)})` queries.

**Formalization Note.** "Constant probability" is every fixed success threshold `p₀ > 0` (§2.1,
p.13: "success thresholds fixed in advance"; proof p.51: "succeed with probability at least a fixed
`p0 > 0` on every promised input"); `Ω_k` is: there are `c > 0` and `N₀` depending only on `k` and
`p₀` such that for all `N ≥ N₀`, every alphabet size `q ≥ N`, every workspace size `w`, every `T`,
every `T`-query algorithm `A` (input-independent start state and unitaries `U_0, …, U_T`, Eq. (5) and
the display after it, p.15) with the phase oracle `O_x|i,c⟩ = ω_q^{c x_i}|i,c⟩`
(`SelectiveDPT.phaseOracle`), and every output map, success probability `≥ p₀` on every exactly
`k`-to-one `x ∈ Z_q^{kN}` forces `T ≥ c (kN)^{(2^{k−1}−1)/(2^k−1)}`. The final PVM is a
computational-basis measurement of the whole register followed by `out` (`SelectiveDPT.successProb`);
with arbitrary `U_T` and workspace this is the class of all PVMs. A successful output is an ordered
`k`-tuple of distinct positions with a common value (`MultiCollQ.collisionRel k 1`). The promised
inputs are `MultiCollQ.exactTypeSet (k*N) q k (pureType k N)`: every value appearing in `x` appears
exactly `k` times (§2.5, p.14). `[n]` is `Fin n` (0-based), `Z_q` is `ZMod q`; `[NeZero q]` excludes
only `q = 0`. The exponent is a real number; `k − 1` is natural subtraction, harmless as `k ≥ 2`. -/
theorem theorem_1_1 (k : ℕ) (hk : 2 ≤ k) (p₀ : ℝ) (hp₀ : 0 < p₀) :
    ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ (q : ℕ) [NeZero q], N ≤ q →
      ∀ (w T : ℕ) (A : QueryAlg (Fin (k * N)) (ZMod q) (Fin w) T)
        (out : (Fin (k * N) × ZMod q) × Fin w → (Fin 1 → Fin k → Fin (k * N))),
        (∀ x ∈ MultiCollQ.exactTypeSet (k * N) q k (MultiCollQ.pureType k N),
          p₀ ≤ SelectiveDPT.successProb A out (MultiCollQ.collisionRel k 1) x) →
        c * ((k * N : ℕ) : ℝ) ^ (((2 : ℝ) ^ (k - 1) - 1) / ((2 : ℝ) ^ k - 1)) ≤ T := by sorry

end QCollLB.Supplement
