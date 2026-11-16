-- Prove2me | Theorems.Thm_QuarticGap_Supplement_theorem_3_10
-- name    : QuarticGap.Supplement.theorem_3_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T01:54:22.208514+00:00
-- url     : https://prove2.me/theorems/2ed84068-5b19-4417-ad1c-8af06dc66fc3
-- title:
--   Theorem 3.10 — Fourier sampling on $K$ characters with $O(\sqrt{M/K}\,(1+\log(1/\varepsilon)))$ quantum queries
-- statement:
--   There is an absolute constant $C > 0$ such that, for every $m \ge 2$, every nonempty set $S \subseteq \{0,1\}^m$ of $K = |S|$ characters and every $\varepsilon \in (0,1)$, there is a quantum algorithm with access to the oracle $O_f|\sigma,c\rangle = |\sigma, c \oplus (1-f(\sigma))/2\rangle$ that makes at most
--   $$
--   C\sqrt{M/K}\,\bigl(1 + \log(1/\varepsilon)\bigr)
--   $$
--   queries and whose output distribution is within total variation distance $\varepsilon$ of $p_{z_f}$ for every Boolean function $f$; that is, it solves $\mathrm{Samp}_S(\varepsilon)$.
--
--   With Theorem 3.9 this gives, for $K = M^\theta$, a separation $\Omega(Q^{2/(1-\theta)}/\log M)$ versus $O(Q)$ with $Q = M^{(1-\theta)/2}$.
--
--   **Formalization Note** One circuit over all unitary gates per $(m, S, \varepsilon)$, fixed before $f$, with an output map to `Option S`; each use of $O_f$, its inverse or its controlled version is one query. The theorem bounds queries, not gates.
--
--   Differences from the source:
--   - reading: a quantum algorithm → an oracle circuit over all unitary gates on any number of wires, fixed before f, started in |0⟩ and measured at the end, with any output map to S ∪ {⊥}; reason: the theorem counts queries only; measurements can be deferred
--   - reading: O(√(M/K)(1 + log(1/ε))) queries → ∃ C > 0 before m, S and ε with at most C√(M/K)(1 + log(1/ε)) queries; reason: the constant of the proof (Lemma 2.8 with r = 1, p₀ = K/(2M)) is absolute; the published Lemma 2.8 is read the same way
--   - encoding: access through the oracle O_f of §2.5 → the published bitOracle (signBit f), its inverse and controlled version counted one query each; reason: this is O_f as published; a controlled phase query uses one call to it (p.18)
--   - encoding: outcomes S ∪ {⊥} → Option S with none = ⊥; reason: the same finite set
-- source:
--   Chakrabarti, Herman, Kim, Ozgul, The Quartic Gap Between Quantum and Dequantized Algorithms for Linear Algebra Is Tight, arXiv:2610.42069 (file sha256 9f68aaf9…), Theorem 3.10, p.28

import Mathlib
import Definitions.Def_QuarticGap_IsCoherentAccess
import Definitions.Def_QuarticGap_Supplement_fourierZ

open QAlgorithms

namespace QuarticGap.Supplement

/-- Theorem 3.10 (arXiv:2610.42069 (file sha256 9f68aaf9…), p.28). For every nonempty `S` and every
`ε ∈ (0, 1)`, a quantum algorithm solves `Samp_S(ε)` with `O(√(M/K) (1 + log(1/ε)))` queries.

**Formalization Note** The algorithm accesses `f` through the oracle `O_f |σ, c⟩ = |σ, c ⊕ (1 −
f(σ))/2⟩` of §2.5 (p.18, and p.27: "A quantum algorithm for `Samp_S` accesses `f` through the oracle
`O_f`"), the published `bitOracle (signBit f)` on `m + 1` wires; each use, of the oracle, its inverse
or its controlled version, counts as one query. The algorithm is one oracle circuit over all unitary
gates, fixed before `f`, started in `|0⟩`, measured in the computational basis, with an output map to
`S ∪ {⊥}` (`Option S`); it must be within `ε` of `p_{z_f}` for every Boolean function `f`. The
constant of `O(·)` is absolute: it comes before `m`, `S` and `ε`. `m ≥ 2` is the standing assumption
of §3.1 (p.21). The theorem bounds queries only, not gates. -/
theorem theorem_3_10 :
    ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ), 2 ≤ m → ∀ (S : Finset (Qubits m)), S.Nonempty →
      ∀ ε : ℝ, 0 < ε → ε < 1 →
      ∃ (N : ℕ) (alg : OracleCircuit UnitaryGates (fun _ : Fin 1 => m + 1) N)
          (out : Qubits N → Option S),
        (totalQueries alg : ℝ) ≤
          C * Real.sqrt (bigM m / S.card) * (1 + Real.log (1 / ε)) ∧
        ∀ f : Qubits m → ℤˣ,
          tv (qOut alg (fun _ => bitOracle (signBit f)) out) (fourierTarget S f) ≤ ε := by sorry

end QuarticGap.Supplement
