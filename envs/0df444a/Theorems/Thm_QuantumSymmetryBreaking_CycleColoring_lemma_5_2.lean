-- Prove2me | Theorems.Thm_QuantumSymmetryBreaking_CycleColoring_lemma_5_2
-- name    : QuantumSymmetryBreaking.CycleColoring.lemma_5_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T21:25:35.95728+00:00
-- url     : https://prove2.me/theorems/878cf4a2-1eaf-4ce5-962d-587f558915fd
-- title:
--   Lemma 5.2 — small normalized POVM energy for every $\varepsilon$ gives one-round cycle $q$-colouring
-- statement:
--   Fix an integer $q\ge2$. Suppose that for every $\varepsilon>0$ there are a dimension $N\in\mathbb N_+$ and a POVM $\{M_a\}_{a\in[q]}$ on $\mathbb C^N\otimes\mathbb C^N$ with
--   $$
--   \frac1{N^3}\sum_{a\in[q]}E(M_a)\le\varepsilon .
--   $$
--   Then for every $\varepsilon>0$ there is a one-way one-round anonymous quantum algorithm that $q$-colours directed cycles so that each edge is monochromatic with probability at most $\varepsilon$.
--
--   Here such an algorithm consists of a state $\rho$ (a density matrix) on finite-dimensional registers $A\otimes B$ and a $q$-outcome POVM $\{P_a\}$ on $B\otimes A$, both chosen before the cycle: on a directed cycle $v_0\to v_1\to\cdots\to v_{n-1}\to v_0$ every node $v_\ell$ prepares $\rho$ on $A_\ell B_\ell$, sends $B_\ell$ to $v_{\ell+1}$, and measures $\{P_a\}$ on $B_{\ell-1}A_\ell$, outputting $c_\ell$. The conclusion is that for every $n\ge3$ and every $i\in\mathbb Z_n$, $\Pr[c_i=c_{i+1}]\le\varepsilon$ under the Born-rule law of the whole $n$-node experiment. The lemma reduces the colouring problem to a statement about single POVMs (a corollary of Gur–Li 2026, Theorem 6.1).
--
--   Differences from the source:
--   - encoding: an algorithm with finite-dimensional registers $A$, $B$ that may use private randomness → a density matrix $\rho$ on $\mathbb C^{d_A}\otimes\mathbb C^{d_B}$ and a POVM $P$ on $B\otimes A$, with the published Born-rule output law `collisionProb`; reason: the published general model of a one-way one-round anonymous algorithm (randomness and workspace absorbed into $\rho$ and $A$); $\rho$ and $P$ are fixed before $n$
--   - reading: “directed cycles” → every directed cycle with $n\ge3$ nodes; reason: for $n=1$ the only edge is a self-loop and $c_0=c_1$ always; for $n=2$ the two edges $v_0\to v_1\to v_0$ form a pair of antiparallel edges, not a cycle graph; the source's directed cycle is a cycle graph (same convention as the published GL26 items)
--   - encoding: colours and outcomes in $[q]$ → `Fin q`; reason: relabelling only
--   - encoding: $E(M)=\operatorname{Tr}(AB)$ → the real part of $\operatorname{Tr}(AB)$ (published `energy` at $\Lambda=I$); reason: the trace is real for PSD $M$, the only operators whose energy the statement uses
-- source:
--   Flin, Li, Suomela, Quantum Advantage for Distributed Symmetry Breaking, STOC 2027 submission #863 (October 2026), source.pdf SHA-256 121c1ecfd6ed3365b5424f6f5978549d12510d800fb87cb8d2f5e110600a542e, Lemma 5.2, p.21 (PDF p.24)

import Mathlib
import Definitions.Def_QuantumSymmetryBreaking_CycleColoring_FiniteRealization
import Definitions.Def_QuantumCycleColoring_FourColor_CycleAlgorithm

open QuantumCycleColoring.FourColor

namespace QuantumSymmetryBreaking.CycleColoring

/-- Lemma 5.2 (corollary of Gur–Li 2026, Theorem 6.1), Flin, Li, Suomela, *Quantum Advantage for Distributed Symmetry Breaking*, STOC 2027 submission #863 (October 2026), p.21 (PDF p.24).
Fix `q ≥ 2`. If for every `ε > 0` there are `N ∈ ℕ⁺` and a POVM `{M_a}_{a ∈ [q]}` on `ℂ^N ⊗ ℂ^N` with
`(1/N^3) ∑_a E(M_a) ≤ ε`, then for every `ε > 0` there is a one-way one-round anonymous quantum
algorithm (a state `ρ` on finite registers `A ⊗ B` and a `q`-outcome POVM `P` on `B ⊗ A`) that `q`-colors
directed cycles so that, on every directed cycle with `n ≥ 3` nodes and every edge `(i, i+1)`,
`Pr[c_i = c_{i+1}] ≤ ε`. -/
theorem lemma_5_2 (q : ℕ) (hq : 2 ≤ q)
    (h : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, 0 < N ∧
      ∃ M : Fin q → Matrix (Fin N × Fin N) (Fin N × Fin N) ℂ,
        IsPOVM M ∧ 1 / (N : ℝ) ^ 3 * ∑ a, energyE (M a) ≤ ε) :
    ∀ ε : ℝ, 0 < ε → ∃ (dA dB : ℕ) (ρ : Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ)
      (P : Fin q → Matrix (Fin dB × Fin dA) (Fin dB × Fin dA) ℂ),
      IsDensityMatrix ρ ∧ IsPOVM P ∧
        ∀ (n : ℕ) [NeZero n], 3 ≤ n → ∀ i : ZMod n, collisionProb n ρ P i ≤ ε := by sorry

end QuantumSymmetryBreaking.CycleColoring
