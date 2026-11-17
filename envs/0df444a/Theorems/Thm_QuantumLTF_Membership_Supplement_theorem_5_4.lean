-- Prove2me | Theorems.Thm_QuantumLTF_Membership_Supplement_theorem_5_4
-- name    : QuantumLTF.Membership.Supplement.theorem_5_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T10:48:28.230455+00:00
-- url     : https://prove2.me/theorems/f3285103-2bf6-4246-a5d6-3a00f42cf679
-- title:
--   Theorem 5.4 — exact $w$-independent band conversion $|F_w^{B_K}\rangle\langle F_w^{B_K}|\mapsto(|w\rangle\langle w|)^{\otimes K}$
-- statement:
--   Let $K\ge1$, $D\ge2K+1$ and $M\ge D$. There is a $w$-independent quantum channel $\mathcal C_{B_K}$ with output on $(\mathbb C^n)^{\otimes K}$ such that, for every unit vector $w$,
--   $$\mathcal C_{B_K}\big(|F_w^{B_K}\rangle\langle F_w^{B_K}|\big)=\big(|w\rangle\langle w|\big)^{\otimes K}.\qquad(183)$$
--   The channel can be implemented using
--   $$O\big(n(\log M+\log(nD))\big)+\tilde O\big(n+K\log(n+1)\big)$$
--   elementary gates and $O(K)$ single-qubit measurements, with no example or membership queries. The $\tilde O$ hides factors polylogarithmic in $K+1$ and $n+1$, but not $\log M$.
--
--   **Formalization Note** $M=2^q$. The channel is a circuit, one round of single-qubit computational-basis measurements, a circuit chosen by the outcomes, and a partial trace onto $K$ output registers (`measChannelOut`). The gate count of a run is the sum of the two circuit sizes. (183) is an exact equality of density matrices.
--
--   Differences from the source:
--   - reading: a w-independent quantum channel implemented with elementary gates and O(K) single-qubit measurements → measChannelOut: a gates12 circuit V on the band state followed by e clean ancillas, a computational-basis measurement of r ≤ C K designated qubits with outcome t, a gates12 circuit W_t, and the partial trace onto K output registers of s qubits (n ≤ 2^s, Cⁿ embedded by binary labels); all chosen before w; gate count |V| + |W_t| for every t; reason: the channel of the proof (p. 69): measure blank markers, then a classically controlled permutation
--   - encoding: O(n(log M + log(nD))) + Õ(n + K log(n+1)) → C n (log 2^q + log(nD)) + C (n + K log(n+1)) log^{K'}((K+1)(n+1)), C and K' fixed before n, K, D, M; reason: Õ hides polylog factors in K + 1 and n + 1 only; log natural
-- source:
--   Krivcenko, Nguyen, de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, arXiv:2609.40331, Theorem 5.4, Eq. (183), p. 67 (PDF p. 68); proof, pp. 67–69 (PDF pp. 68–70)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Circuit
import Definitions.Def_QuantumLTF_Membership_gates12
import Definitions.Def_QuantumLTF_Membership_Supplement_bandKet
import Definitions.Def_QuantumLTF_Membership_Supplement_padKet
import Definitions.Def_QuantumLTF_Membership_Supplement_measChannelOut
import Definitions.Def_QuantumLTF_Membership_Supplement_dirTensorPow

namespace QuantumLTF.Membership.Supplement

open QAlgorithms QuantumLTF.Membership

/-- **Theorem 5.4 (Efficient band conversion).** Krivcenko, Nguyen, de Wolf, *Fast Quantum Algorithms for Learning Linear Threshold Functions*,
arXiv:2609.40331, Theorem 5.4, p. 67 (PDF p. 68): "Let `K ≥ 1`,
`D ≥ 2K + 1`, and `M ≥ D`. There exists a `w`-independent quantum channel `C_{B_K}` with output on
`(Cⁿ)^{⊗K}` such that `C_{B_K}(|F_w^{B_K}⟩⟨F_w^{B_K}|) = (|w⟩⟨w|)^{⊗K}` (183). The channel can be
implemented using `O(n(log M + log(nD))) + Õ(n + K log(n + 1))` elementary gates and `O(K)`
single-qubit measurements, with no additional example or membership queries. Here the `Õ` notation
hides factors polylogarithmic in `K + 1` and `n + 1`, but not `log M`."

**Formalization Note.** `M = 2^q`. The input `|F_w^{B_K}⟩` is `bandKet` on the `n` degree registers
(`n q` wires, degrees in binary), followed by `e` clean ancillas. The channel is fixed before `w`: a
`gates12` circuit `V`, a computational-basis measurement of `r ≤ C K` single qubits `meas` with
outcome `t`, a `gates12` circuit `W t` chosen by `t`, and the partial trace onto `K` output registers
of `s` qubits (`out`, register `k` on output wires `k s, …, k s + s − 1`; `Cⁿ` embedded by the labels
`natToBits s i`, `i < n`, so `n ≤ 2^s`); see `measChannelOut`. No oracle appears. Gate count of the run
with outcome `t`: `|V| + |W t|`. The `Õ` term is `C (n + K log(n+1)) log^{K'}((K+1)(n+1))` (the
`M`-dependence is only the first term); `C, K'` are fixed before `n, K, D, M`. (183) is an exact
equality of density matrices. -/
theorem theorem_5_4 :
    ∃ C : ℝ, 0 < C ∧ ∃ K' : ℕ,
      ∀ (n K D q : ℕ), 1 ≤ K → 2 * K + 1 ≤ D → D ≤ 2 ^ q →
        ∃ (s e r : ℕ) (V : Circuit gates12 (n * q + e)) (W : Qubits r → Circuit gates12 (n * q + e))
          (meas : Fin r ↪ Fin (n * q + e)) (out : Fin (K * s) ↪ Fin (n * q + e)),
          n ≤ 2 ^ s ∧ (r : ℝ) ≤ C * K ∧
          (∀ t : Qubits r, ((V.size + (W t).size : ℕ) : ℝ) ≤
            C * n * (Real.log (2 ^ q) + Real.log (n * D)) +
              C * (n + K * Real.log (n + 1)) * Real.log ((K + 1) * (n + 1)) ^ K') ∧
          ∀ w : EuclideanSpace ℝ (Fin n), ‖w‖ = 1 →
            measChannelOut V.unitary (fun t => (W t).unitary) meas out
              (padKet e (bandKet n q K w)) = dirTensorPow s K w := by sorry

end QuantumLTF.Membership.Supplement
