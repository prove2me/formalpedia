-- Prove2me | Theorems.Thm_QAlgorithms_Nannicini_separation_from_quantumMembership
-- name    : QAlgorithms.Nannicini.separation_from_quantumMembership
-- status  : Open
-- author  : @Goku
-- created : 2026-10-13T17:47:23.326935+00:00
-- url     : https://prove2.me/theorems/756897eb-c997-4832-a15d-0a2ae520a850
-- title:
--   Separation oracle from polylogarithmically many calls to a quantum membership oracle (corrected)
-- statement:
--   This is a corrected form of the quantum construction of a separation oracle from a membership oracle.
--
--   **Quantum membership oracle.** Points of $\mathbb{R}^d$ are written in an $m$-qubit register through an encoding $p \mapsto \mathrm{enc}(p)$. A quantum oracle implementing $\mathrm{MEM}_{0,\epsilon'}(K)$ is a unitary $O$ acting on the point register, an answer qubit and $k$ workspace qubits. On every basis point it acts as
--
--   $$
--   O\,|p\rangle|0\rangle|0^k\rangle = |p\rangle|\varphi_p\rangle ,
--   $$
--
--   where measuring the answer qubit of $\varphi_p$ returns the correct membership bit $[\mathrm{enc}(p) \in K]$ with probability at least $1-\epsilon'$.
--
--   **Separation oracle.** $\mathrm{SEP}_{\epsilon,\delta}(x)$ (Definition 5.22) must, with probability at least $1-\delta$, either assert $x \in B_2(K,\epsilon)$ or return a unit vector $g$ with $\langle g, y\rangle \le \langle g, x\rangle + \epsilon$ for all $y \in B_2(K,-\epsilon) = \{y : B_2(y,\epsilon) \subseteq K\}$.
--
--   **Theorem.** There are absolute constants $C > 0$ and $c \in \mathbb{N}$ with the following property. Let $d \in \mathbb{N}$ and $r, R, \epsilon, \delta \in \mathbb{R}$ with $0 < r < R$, $0 < \epsilon < R$ and $0 < \delta < 1/3$. Then there is $\epsilon' > 0$ such that for every $x \in \mathbb{R}^d$ there exist an encoding $\mathrm{enc}$ and, for every workspace size $k$, a quantum circuit with measurement decoding. The circuit makes at most
--
--   $$
--   C\,\bigl(\log(2+d) + \log(2+R) + \log(2+1/r) + \log(2+1/\epsilon) + \log(2+1/\delta)\bigr)^{c}
--   $$
--
--   uncontrolled calls to the oracle or its inverse. It correctly implements $\mathrm{SEP}_{\epsilon,\delta}(x)$ for every convex $K$ with $B_2(0,r) \subseteq K \subseteq B_2(0,R)$ and $x \notin B_2(K,-\epsilon)$, and for every unitary implementing $\mathrm{MEM}_{0,\epsilon'}(K)$.
--
--   Classically, separation from membership needs $\tilde O(d)$ membership calls. This result gives an exponential improvement in the dimension for the query complexity of convex optimization with a membership oracle.
--
--   **Formalization Note** The source leaves several objects open: the unitary implementing $\mathrm{MEM}$, the value of $\epsilon'$, and the parameters hidden in $\tilde O(1)$. The statement makes each of them explicit. The unit-norm requirement on $g$ is added because Definition 5.22 as printed accepts $g = 0$, which would make the separation oracle trivial.
-- source:
--   Giacomo Nannicini, Quantum algorithms for optimizers, 2025, v5; notes dated 9 July 2025, PDF p. 123, Theorem 5.33. https://arxiv.org/pdf/2408.07086v5

import Definitions.Def_QAlgorithms_Defs_GradientMethods
import Definitions.Def_QAlgorithms_Nannicini_Ch05c_Model
set_option autoImplicit false

namespace QAlgorithms.Nannicini












/-- Corrected statement. Nannicini p.123, Theorem 5.33, as printed: "Let `K ⊂ ℝ^d` be a convex
set satisfying `B₂(0, r) ⊂ K ⊂ B₂(0, R)` for given `r, R ∈ ℝ`, `0 < r < R`, and let
`x ∉ B(K, −ϵ)`. For any `ϵ, δ ∈ ℝ`, `0 < ϵ < R`, `0 < δ < 1/3`, we can implement `SEP_{ϵ,δ}(x)`
with `Õ(1)` calls to a quantum oracle implementing `MEM_{0,ϵ′}(K)`, for an appropriately chosen
`ϵ′`."

What was changed. (1) "A quantum oracle implementing `MEM_{0,ϵ′}(K)`" is made a definition,
`IsQuantumMembershipOracle` (point register preserved, answer correct with probability
`≥ 1 − ϵ′` on every basis point; adjoint calls allowed, controlled calls not). The algorithm
chooses how points are written in qubits (`enc`); it must work for **every** such oracle, for
every workspace size `k` of the oracle and every admissible `K`. (2) "Appropriately chosen `ϵ′`"
is an existential `ϵ′ > 0` depending only on `d, r, R, ϵ, δ`, chosen before `x`, `K` and the
oracle. An oracle meeting the specification for `ϵ′` meets it for every larger value, so this is
"for every sufficiently accurate oracle". It does not trivialize the claim: the content is the
query count. (3) `Õ(1)` is `C · (log(2+d) + log(2+R) + log(2+1/r) + log(2+1/ϵ) + log(2+1/δ))^c`
with absolute `C, c` (Def. 1.11: polylogarithmic in the suppressed instance parameters).
(4) The returned separating vector must have `‖g‖₂ = 1`. Def. 5.22 as printed lets `g = 0`
satisfy `⟨g, y⟩ ≤ ⟨g, x⟩ + ϵ`, which would make `SEP` answerable with no query at all.

Why. The source leaves `ϵ′`, the quantum oracle model and the parameters hidden in `Õ(1)`
unpinned, and its proof is a sketch through Prop. 5.25 (iii) and Prop. 5.31. The statement
asserts only what the theorem sentence claims, with these choices visible.

Output. The algorithm is a circuit on `n` qubits started in `|0⟩` and measured in the
computational basis; the outcome is decoded by `out` into the assertion `x ∈ B₂(K, ϵ)` (`none`)
or a vector `g` (`some g`). The decoding is fixed before `K` and the oracle. -/
theorem separation_from_quantumMembership :
    ∃ C : ℝ, 0 < C ∧ ∃ c : ℕ, ∀ (d : ℕ) (r R ε δ : ℝ), 0 < r → r < R → 0 < ε → ε < R →
      0 < δ → δ < 1 / 3 →
      ∃ ε' : ℝ, 0 < ε' ∧ ∀ x : EuclideanSpace ℝ (Fin d),
        ∃ (m : ℕ) (enc : Qubits m → EuclideanSpace ℝ (Fin d)), ∀ k : ℕ,
          ∃ (n : ℕ) (circ : OracleCircuit twoQubitGateSet (fun _ : Fin 1 => m + (k + 1)) n)
            (out : Qubits n → Option (EuclideanSpace ℝ (Fin d))),
            (circ.queryCount 0 : ℝ) ≤ C * (Real.log (2 + d) + Real.log (2 + R) +
              Real.log (2 + 1 / r) + Real.log (2 + 1 / ε) + Real.log (2 + 1 / δ)) ^ c ∧
            (∀ s ∈ circ, uncontrolledStep s) ∧
            ∀ K : Set (EuclideanSpace ℝ (Fin d)), Convex ℝ K →
              Metric.closedBall 0 r ⊆ K → K ⊆ Metric.closedBall 0 R →
              x ∉ {y | Metric.closedBall y ε ⊆ K} →
              ∀ O : Matrix (Qubits (m + (k + 1))) (Qubits (m + (k + 1))) ℂ,
                IsQuantumMembershipOracle K enc ε' O →
                1 - δ ≤ (open Classical in
                  probEvent (act (circ.unitary fun _ => O) (zeroKet n)) fun z =>
                    match out z with
                    | none => ∃ y ∈ K, dist x y ≤ ε
                    | some g => ‖g‖ = 1 ∧ ∀ y, Metric.closedBall y ε ⊆ K →
                        inner ℝ g y ≤ inner ℝ g x + ε) := by
  sorry

end QAlgorithms.Nannicini
