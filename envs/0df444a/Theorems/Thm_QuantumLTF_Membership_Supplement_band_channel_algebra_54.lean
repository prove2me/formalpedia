-- Prove2me | Theorems.Thm_QuantumLTF_Membership_Supplement_band_channel_algebra_54
-- name    : QuantumLTF.Membership.Supplement.band_channel_algebra_54
-- status  : Proved
-- author  : @Robin Kothari
-- created : 2026-11-25T01:13:17.9004+00:00
-- url     : https://prove2.me/theorems/d1f9d70c-09bf-4bd3-977f-46ab6f0e9174
-- title:
--   Multivariate Hermite-to-multinomial channel collapse on Hermite band states
-- statement:
--   Let $n, K, D, q, e \in \mathbb{N}$ satisfy $n \ge 1$, $K \ge 1$, and $2K + 1 \le D \le 2^q$, and set $s = \lceil \log_2 n \rceil + 1$ so that the $(n+1)$-letter alphabet $\{0, 1, \dots, n-1, \perp\}$ is injectively encoded into $s$-bit strings (nonblank labels $i \in \{0,\dots,n-1\}$ have most significant bit $0$, whereas the blank symbol $\perp$ has most significant bit $1$). Consider a quantum system of $nq + e$ qubits containing an embedded $2K$-register particle block of $2Ks$ wires (indexed by an injection $\mathrm{partEmb}$), a $2K$-qubit measurement wire set $\mathrm{meas}$ reading the most significant bit of each particle register, and a $K$-register output block $\mathrm{out}$ coinciding with the first $K$ particle registers.
--
--   Suppose $V$ is a linear operator on $\mathbb{C}^{2^{nq+e}}$ that maps every valid occupation-number basis state $|\alpha\rangle|0^e\rangle$ with total degree $k = |\alpha| = \sum_{i=1}^n \alpha_i \in [K, 2K]$ to the normalized symmetric multinomial superposition $|\Phi_\alpha\rangle$ (`multinomKet54`) on the $2K$-register particle block tensored with a degree-dependent basis state $|\mathrm{deg}(k)\rangle$ on all remaining wires. Suppose further that for every $2K$-bit measurement outcome $t \in \{0,1\}^{2K}$ containing at least $K$ zeros (nonblank flags), the conditional operator $W(t)$ acts as a register permutation $\sigma \in S_{2K}$ on the particle block, fixing all non-particle wires and routing $K$ nonblank positions $\sigma(0), \dots, \sigma(K-1)$ (where $t_{\sigma(r)} = 0$) into the first $K$ output registers $\mathrm{out}$.
--
--   Let $|F_w^{B_K}\rangle$ denote the normalized Hermite degree-band state associated with the sign function $f_w(x) = \mathrm{sign}(\langle w, x\rangle)$ for a unit vector $w \in \mathbb{S}^{n-1}$, and let $|w\rangle = \sum_{i=0}^{n-1} w_i |i\rangle \in \mathbb{C}^{2^s}$ denote its encoded direction state. Then applying $V$, measuring the $2K$ blank-indicator bits, applying the conditional compaction $W(t)$, and tracing out all wires outside $\mathrm{out}$ maps $|F_w^{B_K}\rangle|0^e\rangle$ exactly to the $K$-fold tensor power of $|w\rangle$:
--
--   $$
--   \mathcal{C}_{B_K}\!\bigl(|F_w^{B_K}\rangle\langle F_w^{B_K}| \otimes |0^e\rangle\langle 0^e|\bigr) = \bigl(|w\rangle\langle w|\bigr)^{\otimes K}.
--   $$
--
--   This algebraic collapse theorem isolates the multivariate Hermite-to-multinomial cancellation and partial-trace computation needed to prove correctness of the efficient band-conversion channel in Theorem 5.4 of Krivcenko, Nguyen, and de Wolf (2026).
--
--   **Formalization Note** Here `bandKet n q K w` represents $|F_w^{B_K}\rangle$, `padKet e` appends $|0^e\rangle$, `measChannelOut V W meas out` computes the partial trace over wires outside `out` after applying `V`, projecting onto measurement outcomes `t` on `meas`, and applying `W t`, and `dirTensorPow s K w` denotes the matrix $(|w\rangle\langle w|)^{\otimes K}$ on `Qubits (K * s)`.
-- source:
--   Krivcenko, Nguyen, de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, arXiv:2609.40331, Section 5.3, Theorem 5.4 and its proof (pp. 66-69, PDF pp. 67-70; Eqs. (182)-(184) and the channel computation on pp. 68-69).

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QuantumLTF_Membership_flatReg
import Definitions.Def_QuantumLTF_Membership_splitReg
import Definitions.Def_QuantumLTF_Membership_Supplement_bandKet
import Definitions.Def_QuantumLTF_Membership_Supplement_padKet
import Definitions.Def_QuantumLTF_Membership_Supplement_dirTensorPow
import Definitions.Def_QuantumLTF_Membership_Supplement_measChannelOut
import Definitions.Def_QuantumLTF_Membership_Supplement_symBand54

set_option autoImplicit false

namespace QuantumLTF.Membership.Supplement

open QAlgorithms QuantumLTF.Membership

theorem band_channel_algebra_54 :
    ∀ (n K D q e : ℕ), 1 ≤ n → 1 ≤ K → 2 * K + 1 ≤ D → D ≤ 2 ^ q →
      let s := Nat.clog 2 n + 1
      ∀ (partEmb : Fin (2 * K * s) ↪ Fin (n * q + e))
        (meas : Fin (2 * K) ↪ Fin (n * q + e))
        (out : Fin (K * s) ↪ Fin (n * q + e))
        (V : Matrix (Qubits (n * q + e)) (Qubits (n * q + e)) ℂ)
        (W : Qubits (2 * K) → Matrix (Qubits (n * q + e)) (Qubits (n * q + e)) ℂ)
        (degState : ℕ → Qubits (n * q + e)),
        (∀ j : Fin (2 * K), meas j = partEmb (finProdFinEquiv (j, ⟨0, Nat.succ_pos _⟩))) →
        (∀ (k : Fin K) (j : Fin s),
          out (finProdFinEquiv (k, j)) = partEmb (finProdFinEquiv (⟨k.val, by omega⟩, j))) →
        (∀ (α : Fin n → ℕ) (hk : K ≤ ∑ i, α i ∧ ∑ i, α i ≤ 2 * K),
          act V (padKet e (ket (flatReg n q fun i => natToBits q (α i)))) =
            embedPartAndDeg54 partEmb (multinomKet54 n s K α hk) (degState (∑ i, α i))) →
        (∀ t : Qubits (2 * K), K ≤ (Finset.univ.filter fun j => t j = false).card →
          ∃ σ : Equiv.Perm (Fin (2 * K)),
            (∀ k : Fin K, t (σ ⟨k.val, by omega⟩) = false) ∧
            ∀ x : Qubits (n * q + e),
              act (W t) (ket x) = ket (permPartReg54 partEmb σ x)) →
        ∀ w : EuclideanSpace ℝ (Fin n), ‖w‖ = 1 →
          measChannelOut V W meas out (padKet e (bandKet n q K w)) = dirTensorPow s K w := by sorry

end QuantumLTF.Membership.Supplement
