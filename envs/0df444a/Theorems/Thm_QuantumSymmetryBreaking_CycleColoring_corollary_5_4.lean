-- Prove2me | Theorems.Thm_QuantumSymmetryBreaking_CycleColoring_corollary_5_4
-- name    : QuantumSymmetryBreaking.CycleColoring.corollary_5_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T21:25:35.289229+00:00
-- url     : https://prove2.me/theorems/f904b06d-7bf7-406f-b998-3300e67d8718
-- title:
--   Corollary 5.4 — one-round quantum colouring of directed cycles with $2\cdot10^4$ colours and per-edge failure $\le\varepsilon$
-- statement:
--   For every $\varepsilon>0$ there is a one-way one-round anonymous quantum algorithm that colours directed cycles with $q=2\cdot10^4$ colours so that each edge is monochromatic with probability at most $\varepsilon$.
--
--   Precisely: there are finite dimensions $d_A,d_B$, a density matrix $\rho$ on $\mathbb C^{d_A}\otimes\mathbb C^{d_B}$ and a POVM $\{P_a\}_{a\in[q]}$ on $\mathbb C^{d_B}\otimes\mathbb C^{d_A}$, depending on $\varepsilon$ only, such that on every directed cycle $v_0\to\cdots\to v_{n-1}\to v_0$ with $n\ge3$ nodes — where every node $v_\ell$ prepares $\rho$ on $A_\ell B_\ell$, sends $B_\ell$ to $v_{\ell+1}$, measures $\{P_a\}$ on $B_{\ell-1}A_\ell$ and outputs the outcome $c_\ell$ — and for every edge $(v_i,v_{i+1})$,
--   $$
--   \Pr[c_i=c_{i+1}]\le\varepsilon ,
--   $$
--   the probability being given by Born's rule for the measurement $\bigotimes_\ell P_{c_\ell}$ on $\rho^{\otimes n}$.
--
--   This is Result 1 of the paper, the basis of all its algorithmic results: the number of colours does not depend on $\varepsilon$, only the dimension does.
--
--   Differences from the source:
--   - encoding: an algorithm with finite-dimensional registers $A$, $B$ that may use private randomness → a density matrix $\rho$ on $\mathbb C^{d_A}\otimes\mathbb C^{d_B}$ and a POVM $P$ on $B\otimes A$, with the published Born-rule output law `collisionProb`; reason: the published general model of a one-way one-round anonymous algorithm (randomness and workspace absorbed into $\rho$ and $A$); $\rho$ and $P$ are fixed before $n$
--   - reading: “directed cycles” → every directed cycle with $n\ge3$ nodes; reason: for $n=1$ the only edge is a self-loop and $c_0=c_1$ always; for $n=2$ the two edges $v_0\to v_1\to v_0$ form a pair of antiparallel edges, not a cycle graph; the source's directed cycle is a cycle graph (same convention as the published GL26 items)
--   - encoding: $q=2\cdot10^4$ colours → `Fin (2 * 10 ^ 4)`; reason: relabelling only
-- source:
--   Flin, Li, Suomela, Quantum Advantage for Distributed Symmetry Breaking, STOC 2027 submission #863 (October 2026), source.pdf SHA-256 121c1ecfd6ed3365b5424f6f5978549d12510d800fb87cb8d2f5e110600a542e, Corollary 5.4, p.22 (PDF p.25)

import Mathlib
import Definitions.Def_QuantumSymmetryBreaking_CycleColoring_FiniteRealization
import Definitions.Def_QuantumCycleColoring_FourColor_CycleAlgorithm

open QuantumCycleColoring.FourColor

namespace QuantumSymmetryBreaking.CycleColoring

/-- Corollary 5.4, Flin, Li, Suomela, *Quantum Advantage for Distributed Symmetry Breaking*, STOC 2027 submission #863 (October 2026), p.22 (PDF p.25); the paper's Result 1.
For every `ε > 0` there is a one-way one-round anonymous quantum algorithm — every node prepares the same
state `ρ` on finite registers `A ⊗ B`, sends `B` to its successor, and measures the same
`q`-outcome POVM `P` (`q = 2 · 10^4`) on (received `B`, own `A`) — chosen before the cycle, such that on
every directed cycle with `n ≥ 3` nodes and every edge `(i, i+1)`, the Born-rule probability of
`c_i = c_{i+1}` is at most `ε`. -/
theorem corollary_5_4 (ε : ℝ) (hε : 0 < ε) :
    ∃ (dA dB : ℕ) (ρ : Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ)
      (P : Fin (2 * 10 ^ 4) → Matrix (Fin dB × Fin dA) (Fin dB × Fin dA) ℂ),
      IsDensityMatrix ρ ∧ IsPOVM P ∧
        ∀ (n : ℕ) [NeZero n], 3 ≤ n → ∀ i : ZMod n, collisionProb n ρ P i ≤ ε := by sorry

end QuantumSymmetryBreaking.CycleColoring
