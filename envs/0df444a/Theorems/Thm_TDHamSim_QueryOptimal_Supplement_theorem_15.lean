-- Prove2me | Theorems.Thm_TDHamSim_QueryOptimal_Supplement_theorem_15
-- name    : TDHamSim.QueryOptimal.Supplement.theorem_15
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:14:50.152908+00:00
-- url     : https://prove2.me/theorems/2643e114-32ff-4ee7-8c05-d18367aef88f
-- title:
--   Theorem 15 — gate-efficient integrated-norm scaling
-- statement:
--   Let $T>0$, let $H:[0,T]\to\mathrm{Herm}(\mathcal H_S)$ be $\beta$-Lipschitz, and let $h:[0,T]\to[0,\infty)$ be $\beta_h$-Lipschitz with $\|H(t)\|\le h(t)$. Let $0<\varepsilon\le1/2$, set $\Lambda_h=\int_0^T h(t)\,dt$, and suppose $\Lambda_h>\varepsilon$. The algorithm has query access to the reparameterized oracle $\mathrm{HAM\text{-}T}^{L^1}_J=\sum_j|j\rangle\langle j|\otimes O_j$ of Definition 4 at a power-of-two resolution $J$ of its choice: each $O_j$ acts on an $a$-qubit register and the system, is Hermitian and unitary, and has zero-ancilla compression $\widetilde H(s_j)$, $s_j=2j\Lambda_h/J$.
--
--   Then there are an absolute constant $C>0$ and, for the given scalar data, a circuit $U_{\rm sim}$ on the system and an auxiliary register $W$ such that for every unit vector $\psi$
--
--   $$\big\|U_{\rm sim}(|0\rangle_W\psi)-|0\rangle_W\,U_H(T)\psi\big\|\le\varepsilon,$$
--
--   the circuit makes at most $C\,q_{L^1}$ queries, where
--
--   $$q_{L^1}=\Lambda_h+\frac{\log(1/\varepsilon)}{\log\big(e+\log(1/\varepsilon)/\Lambda_h\big)},$$
--
--   and it uses at most $C\,n_{\rm anc}$ auxiliary qubits and at most $C\,q_{L^1}n_{\rm anc}$ additional one- and two-qubit gates, where
--
--   $$n_{\rm anc}=a+\log\Big(1+\frac{\Lambda_h+(\beta+\beta_h)T^2}{\varepsilon}\Big).$$
--
--   The theorem replaces the worst-case evolution length $\alpha T$ of the main theorem by the integrated envelope $\Lambda_h$, while the gate and space overheads stay logarithmic. It assumes coherent access to the normalized samples, which is a stronger oracle than the fixed-normalization HAM-T model.
--
--   **Formalization Note** The resolution $J=2^m$, the number of auxiliary wires and the circuit are fixed from $n,a,\beta,\beta_h,T,\Lambda,\varepsilon$ before $H$, $h$ and the oracle blocks, which are then universally quantified subject to the hypotheses and the promise $\int_0^Th=\Lambda$. The error compares the whole output, auxiliary wires included. The circuit consists of one- and two-qubit gates and controlled oracle calls.
--
--   Differences from the source:
--   - encoding: qubit Hilbert space H_S and Herm(H_S) → binary-string basis Bits n, finite complex matrices, the spectral (L2 operator) norm; reason: a change of coordinates representing every source instance; the base mission's convention
--   - encoding: H : [0,T] → Herm(H_S) and h : [0,T] → [0,∞) → functions on ℝ with every hypothesis (Hermitian, Lipschitz, nonnegative, envelope) restricted to [0,T]; reason: values outside [0,T] never enter Λ_h, F, τ, H̃ on their source intervals, or the propagator
--   - encoding: O(q_{L¹}), O(n_anc), O(q_{L¹} n_anc) → one positive absolute real constant C chosen before all parameters bounding the query count, the auxiliary-wire count and the additional-gate count; reason: a single constant dominates the finitely many universal constants; logarithm-base factors are absorbed
--   - encoding: a circuit U_sim for the given instance, with J chosen by the algorithm → m (J = 2^m), k and the circuit are chosen from the scalar data n, a, β, β_h, T, Λ, ε before H, h and the oracle blocks; Λ enters as a promise intNorm h T = Λ; reason: an oracle algorithm is uniform over its oracle; the resource bounds depend only on these scalars (the base goal's convention)
--   - encoding: β, β_h Lipschitz constants → explicit hypotheses 0 ≤ β and 0 ≤ β_h; reason: Lipschitz constants are nonnegative; on every instance with T > 0 this follows from the Lipschitz hypotheses, and it is stated because the circuit is chosen before H and h
--   - encoding: query access to HAM-T^{L¹}_J of (91)–(92) → IsHAMT (Htilde H h T) 1 (2Λ) O (Hermitian unitary blocks with zero-ancilla compression H̃(2jΛ/J)), queried through the base controlledHAMT O, one controlled application counting as one query; reason: Definition 4 is the base HAM-T predicate for H̃ with normalization one and horizon 2Λ_h; the base mission's query convention
-- source:
--   Boyang Chen, Minbo Gao, Zhengfeng Ji, Tongyang Li, Xinzhao Wang, Shuo Zhou, STOC 2027 submission #383 (October 2026), Theorem 15 (Gate-efficient integrated-norm scaling), p.38, with Definition 4, (91)–(92), p.36; proof p.39. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/383.pdf

import Definitions.Def_TDHamSim_QueryOptimal_Supplement_Reparam

open scoped Matrix.Norms.L2Operator

namespace TDHamSim.QueryOptimal.Supplement

open TDHamSim.QueryOptimal

/-- Theorem 15, p.38: with access to the reparameterized oracle `HAM-T^{L¹}_J` (Definition 4,
(91)–(92): Hermitian unitary blocks block-encoding `H̃(s_j)`, `s_j = 2jΛ_h/J`, normalization one),
a fixed circuit, chosen from the scalar data before `H`, `h` and the blocks, simulates `U_H(T)`
to full-output error `ε` with `O(q_{L¹})` queries, `O(n_anc)` auxiliary wires and
`O(q_{L¹} n_anc)` additional one- and two-qubit gates. The constant precedes every parameter. -/
theorem theorem_15 :
    ∃ C : ℝ, 0 < C ∧ ∀ (n a : ℕ) (β βh T Λ ε : ℝ),
      0 ≤ β → 0 ≤ βh → 0 < T → 0 < ε → ε ≤ 1/2 → ε < Λ →
      ∃ m k : ℕ, ∃ c : ConstDepthUnitary.OCircuit (Wires n k) (1+m+a+n),
        c.IsStandard ∧
        (c.queries : ℝ) ≤ C * qL1 Λ ε ∧
        (k : ℝ) ≤ C * nL1 a β βh T Λ ε ∧
        (extraGates c : ℝ) ≤ C * qL1 Λ ε * nL1 a β βh T Λ ε ∧
        ∀ (H : ℝ → Mat (Bits n)) (h : ℝ → ℝ) (O : Fin (2^m) → Mat (Bits a × Bits n)),
          (∀ t ∈ Set.Icc 0 T, (H t).IsHermitian) →
          (∀ s ∈ Set.Icc 0 T, ∀ t ∈ Set.Icc 0 T, opNorm (H t - H s) ≤ β * |t - s|) →
          (∀ t ∈ Set.Icc 0 T, 0 ≤ h t) →
          (∀ s ∈ Set.Icc 0 T, ∀ t ∈ Set.Icc 0 T, |h t - h s| ≤ βh * |t - s|) →
          (∀ t ∈ Set.Icc 0 T, opNorm (H t) ≤ h t) →
          intNorm h T = Λ →
          IsHAMT (Htilde H h T) 1 (2 * Λ) O →
          Simulates c (controlledHAMT O) (propagator H T T) ε := by sorry

end TDHamSim.QueryOptimal.Supplement
