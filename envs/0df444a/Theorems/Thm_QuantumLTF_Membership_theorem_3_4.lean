-- Prove2me | Theorems.Thm_QuantumLTF_Membership_theorem_3_4
-- name    : QuantumLTF.Membership.theorem_3_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:39:14.050201+00:00
-- url     : https://prove2.me/theorems/a03e2f1b-e836-4e37-b373-69ac8c6f982f
-- title:
--   Theorem 3.4 — learning general LTFs from $O(\log(n/\epsilon))$ membership queries and $\tilde O(n)$ gates
-- statement:
--   Let $n\ge2$, $w\in\mathbb S^{n-1}$, $\theta\in\mathbb R$, and suppose that the learner has coherent membership-query access to $f_{w,\theta}$. For every $0<\epsilon\le1/2$ there is a quantum algorithm that outputs a hypothesis $\hat f:\mathbb R^n\to\{-1,+1\}$ such that
--   $$\Pr_{x\sim\gamma_n}\left[\hat f(x)\ne f_{w,\theta}(x)\right]\le\epsilon$$
--   with probability at least $2/3$. It uses $O(\log(n/\epsilon))$ membership queries and $\tilde O(n)$ additional gates, where $\tilde O$ hides polylogarithmic factors in $n$ and $1/\epsilon$.
--
--   Here the algorithm is one oracle circuit, chosen before $w,\theta$ and depending only on $n,\epsilon$, started from $|0\cdots0\rangle$ and measured at the end. Its output is the LTF $f_{a,b}$ whose parameters are fixed-point numbers read from designated wires. It gives an exponential separation from the classical $\Omega(n\log(1/\epsilon))$ query complexity.
--
--   Differences from the source:
--   - reading: O(log(n/ϵ)) and Õ(n) → ∃ C K before n, ϵ: queries ≤ C log(n/ϵ) and gates ≤ C n log^K(n/ϵ); reason: Õ hides polylogarithmic factors in n and 1/ϵ (Table 1, p. 4); the statement gives no exponent, so K is existential
--   - reading: additional gates → unitaries on one or two qubits, all-to-all, clean ancillas; reason: the model of §C.5, p. 95; §3 names no other
--   - encoding: membership queries at points of Rⁿ → queries at fixed-point points of a format (ℓ, f) the circuit picks; reason: the proof queries only such points (p. 33)
--   - generalization: a hybrid quantum algorithm with randomness and classical steps → one unitary circuit from |0…0⟩, measured at the end, classical work counted in gateCount; reason: randomness by Hadamards and adaptivity by deferred measurement purify the algorithm; such a circuit is itself a quantum algorithm with the printed bounds
--   - generalization: a hypothesis f̂ : Rⁿ → {−1, +1} → f̂ is the LTF f_{a,b} with a, b fixed-point numbers read from wires; a = 0 for a constant; reason: p. 33 represents the output this way; a free decoder would hide classical work
--   - reading: for every 0 < ϵ ≤ 1/2 there exists a quantum algorithm → the circuit is nonuniform in n, ϵ; reason: the printed quantifier order; no uniformity is stated
--   - generalization: membership queries, unspecified as to control → every oracle call is plain or inverse, with no control wire; reason: the proof uses no controlled query; an uncontrolled circuit is a special case of a circuit with any queries
--   - reading: let f_{w,θ} be the target, with coherent access; for every ϵ there exists a quantum algorithm → the circuit, its formats and output wires are chosen before w and θ, depending only on n and ϵ; reason: a learner sees the target only through its oracle; the algorithm of pp. 31–33 uses only n and ϵ
-- source:
--   Krivcenko, Nguyen, de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, arXiv:2609.40331, Theorem 3.4, p. 31 (PDF p. 32); Theorem 1.1, p. 6 (PDF p. 7)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Circuit
import Definitions.Def_QuantumLTF_Membership_ltf
import Definitions.Def_QuantumLTF_Membership_disagree
import Definitions.Def_QuantumLTF_Membership_memOracle
import Definitions.Def_QuantumLTF_Membership_gates12
import Definitions.Def_QuantumLTF_Membership_Uncontrolled
import Definitions.Def_QuantumLTF_Membership_readFp

namespace QuantumLTF.Membership

open QAlgorithms

/-- **Theorem 3.4 (Learning general LTFs with Membership Query).** Krivcenko, Nguyen, de Wolf, *Fast Quantum Algorithms for Learning Linear Threshold Functions*,
arXiv:2609.40331, Theorem 3.4, p. 31 (PDF p. 32),
also Theorem 1.1, p. 6 (PDF p. 7). For `n ≥ 2`, `w ∈ S^{n−1}`, `θ ∈ R`, and coherent membership-query access to
`f_{w,θ}`: for every `0 < ϵ ≤ 1/2` there is a quantum algorithm that outputs a hypothesis `f̂` with
`Pr_{x∼γ_n}[f̂(x) ≠ f_{w,θ}(x)] ≤ ϵ` with probability at least `2/3`, using `O(log(n/ϵ))` membership queries
and `Õ(n)` additional gates.

**Formalization Note.** `∃ C K` precede `n, ϵ` (Õ hides polylogarithmic factors in `n` and `1/ϵ`, Table 1,
p. 4). The algorithm is one oracle circuit on `m` wires from `|0…0⟩`, measured at the end, over one- and
two-qubit unitaries (p. 95), with plain queries at fixed-point points of a format `(ℓ, f)`. Its output is the
fixed-point LTF `f_{a,b}` read from the wires `oa`, `ob` (p. 33; a constant hypothesis has `a = 0`). The
circuit and the formats are chosen before `w, θ`. -/
theorem theorem_3_4 :
    ∃ (C : ℝ) (K : ℕ), 0 < C ∧ ∀ n : ℕ, 2 ≤ n → ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 →
      ∃ (ℓ f m ℓo fo : ℕ)
        (c : OracleCircuit gates12 (fun _ : Fin 1 => n * ℓ + 1) m)
        (oa : Fin n → (Fin ℓo ↪ Fin m)) (ob : Fin ℓo ↪ Fin m),
        Uncontrolled c ∧
        (c.queryCount 0 : ℝ) ≤ C * Real.log (n / ε) ∧
        (c.gateCount : ℝ) ≤ C * n * (Real.log (n / ε)) ^ K ∧
        ∀ w : EuclideanSpace ℝ (Fin n), ‖w‖ = 1 → ∀ θ : ℝ,
          open Classical in
          probEvent (act (c.unitary fun _ => memOracle n ℓ f w θ) (zeroKet m))
            (fun z => disagree
              (ltf (WithLp.toLp 2 fun i => readFp (oa i) fo z) (readFp ob fo z))
              (ltf w θ) ≤ ε) ≥ 2 / 3 := by sorry

end QuantumLTF.Membership
