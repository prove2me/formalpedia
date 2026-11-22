-- Prove2me | Theorems.Thm_TolProdTest_theorem_3_8_implementation
-- name    : TolProdTest.theorem_3_8_implementation
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T03:27:26.27692+00:00
-- url     : https://prove2.me/theorems/740ccc5d-a626-4376-b0fb-577ead991da0
-- title:
--   Theorem 3.8, proof — implementation step: a circuit with $nT\,\mathrm{poly}(k,\log d,\log(nT/\delta))$ gates within $\delta/2$ of the ideal protocol
-- statement:
--   There is an absolute constant $C_2>0$ such that for all $1\ge a>b\ge0$, $\delta\in(0,1/2)$, $n\ge1$, $d\ge2$, with $k,T$ the parameters of Protocol 3.1, there is a quantum circuit over the gate set $\{H,S,T,X,\mathrm{CNOT}\}$ acting on $T\cdot k$ encoded copies of the input and ancillas in $|0\rangle$, with at most
--
--   $$
--   C_2\,n\,T\,\Big(k+\log d+\log\frac{nT}{\delta}\Big)^{C_2}
--   $$
--
--   gates, whose acceptance probability differs from that of the ideal Protocol 3.1 by at most $\delta/2$ on every density operator $\rho$ on $(\mathbb C^d)^{\otimes n}$.
--
--   This is the implementation step of Theorem 3.8: each local symmetric-subspace measurement is realized with the Schur transform to accuracy $\delta/(2nT)$.
--
--   Differences from the source:
--   - reading: an algorithm (the paper names no computational model); computational complexity → a list of gates over {H, S, T, X, CNOT} (published ShiShallow.Instr) on N encoded copies of ρ plus m ancillas in |0⟩, fixed before ρ; it answers 'F_prod(ρ) ≥ a' iff wire out reads 1 (acceptProbMixed); computational complexity = number of gates; reason: Theorem 3.8 counts quantum gates; a fixed finite universal gate set is the stronger reading (Solovay–Kitaev relates any two at polylog cost); intermediate measurements and the classical threshold are deferred into the circuit
--   - encoding: copies of an n-qudit state given to the algorithm → each qudit on Nat.clog 2 d qubit wires, level in little-endian binary, copy j site i on wires (j·n+i)·⌈log₂ d⌉, …; input ρ^{⊗N} = ShadowTomography.UpperBound.tensorPow ρ N; reason: any fixed injective encoding differs by a relabelling of wires, which costs no gates
--   - encoding: ρ ∈ D((ℂ^d)^{⊗n}), n ≥ 1, d ≥ 2 → ρ : Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ with WildeQIT.IsDensityOperator ρ (positive semidefinite, trace 1); reason: the computational basis of (ℂ^d)^{⊗n} is indexed by level strings Fin n → Fin d; same operators, sites and levels 0-based
--   - reading: poly(k, log d, log(nT/δ)) gates per register, nT registers → C₂ · n · T · (k + log d + log(nT/δ))^{C₂} with one absolute C₂ > 0; reason: a polynomial in nonnegative arguments whose sum is ≥ 1 is bounded by C(sum)^C
--   - reading: each binary measurement implemented to half-diamond-norm error δ/(2nT) changes the decision probability by at most δ/2 → |acceptProbMixed − idealAccept| ≤ δ/2 for every density operator; reason: the conclusion the hybrid argument delivers
--   - encoding: the parameters c, η, q, R, k, p_Y, p_N, T of (67)–(70) with ceilings → protoC, protoEta, protoQ, protoR, protoK, protoPY, protoPN, protoT with ⌈·⌉₊ (Nat.ceil) and the natural logarithm; reason: all ceiling arguments are positive under 1 ≥ a > b ≥ 0, δ ∈ (0,1/2); log is natural (p.8)
--   - encoding: the decision probability of Protocol 3.1 with exact local measurements → idealAccept = Re Tr(P ρ^{⊗Tk}), P the threshold operator over T trials of {Q_k, I − Q_k}, trial j on copies jk, …, jk+k−1; reason: the Born rule for commuting projective measurements on disjoint copies
-- source:
--   Bao, Helsen, Nguyen, Fully tolerant product state testing and closest product state learning, arXiv:2610.01979 (version of October 1st 2026, sha256 9e43ab25…), proof of Theorem 3.8, eq. (79), p.19

import Mathlib
import Definitions.Def_TolProdTest_idealAccept
import Definitions.Def_TolProdTest_acceptProbMixed
import Definitions.Def_WildeQIT_IsDensityOperator

set_option autoImplicit false

open Matrix

namespace TolProdTest

/-- **Proof of Theorem 3.8, implementation step**, Bao, Helsen, Nguyen, *Fully tolerant product state testing and closest product state learning*, arXiv:2610.01979 (version of October 1st 2026, sha256 9e43ab25…), eq. (79), p.19: "Each trial makes one local
symmetric-subspace measurement at each of the n sites. Implementing each binary measurement to half-diamond-norm
channel error at most δ/(2nT) changes the final decision probability by at most δ/2 by a hybrid argument. … The
corrected high-dimensional Schur transform of Burchardt et al. [BFG+25, Theorem 1], followed by measurement of the
irrep label (k), implements each local projector using poly(k, log d, log(nT/δ)) gates per register, giving
nT poly(k, log d, log(nT/δ)) = 2^{Õ(∆^{−5})} n poly(log(2nd/δ)) (79) gates in total."

There is an absolute constant `C₂ > 0` such that for all parameters there is a circuit over `{H, S, T, X, CNOT}` on
the `T·k` encoded copies plus ancillas, with at most `C₂ · n · T · (k + log d + log(nT/δ))^{C₂}` gates, whose
acceptance probability is within `δ/2` of that of the ideal Protocol 3.1 on every density operator.

**Formalization Note** Circuits, encoding and acceptance are as in `acceptProbMixed` (the circuit is chosen before
`ρ`); `poly(k, log d, log(nT/δ))` is read as `C₂ (k + log d + log(nT/δ))^{C₂}`. Standing assumptions (§3.4):
`1 ≥ a > b ≥ 0`, `δ ∈ (0, 1/2)`, `n ≥ 1`, `d ≥ 2`. -/
theorem theorem_3_8_implementation :
    ∃ C₂ : ℝ, 0 < C₂ ∧ ∀ a b δ : ℝ, 0 ≤ b → b < a → a ≤ 1 → 0 < δ → δ < 1 / 2 →
      ∀ n d : ℕ, 1 ≤ n → 2 ≤ d →
      ∃ (m : ℕ) (out : Fin (protoT a b δ * protoK a b * n * qd d + m))
        (gates : List (ShiShallow.Instr (protoT a b δ * protoK a b * n * qd d + m))),
        (gates.length : ℝ) ≤ C₂ * n * (protoT a b δ : ℝ) *
          ((protoK a b : ℝ) + Real.log d + Real.log (n * (protoT a b δ : ℝ) / δ)) ^ C₂ ∧
        ∀ ρ : Matrix (Config n d) (Config n d) ℂ, WildeQIT.IsDensityOperator ρ →
          |acceptProbMixed (ShadowTomography.UpperBound.tensorPow ρ (protoT a b δ * protoK a b)) gates out -
            idealAccept n d a b δ ρ| ≤ δ / 2 := by sorry

end TolProdTest
