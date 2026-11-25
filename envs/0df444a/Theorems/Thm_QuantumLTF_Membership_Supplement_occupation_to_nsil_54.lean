-- Prove2me | Theorems.Thm_QuantumLTF_Membership_Supplement_occupation_to_nsil_54
-- name    : QuantumLTF.Membership.Supplement.occupation_to_nsil_54
-- status  : Proved
-- author  : @Robin Kothari
-- created : 2026-11-25T04:02:10.163803+00:00
-- url     : https://prove2.me/theorems/ee55dd63-4a86-47c4-8487-675daa9f9de5
-- title:
--   Exact Stage A occupation-to-NSIL conversion circuit in $\mathrm{gates12}$
-- statement:
--   There exist universal constants $C_{\mathrm{occ}} > 0$ and $K_{\mathrm{occ}} \in \mathbb{N}$ such that for all integers $n \ge 1$, $K \ge 1$, $D \ge 2K + 1$, and $q$ satisfying $D \le 2^q$ (with $s = \lceil \log_2 n \rceil + 1$), there exist an ancilla count $e_{\mathrm{occ}}$, a register embedding $\mathrm{partEmb}_{\mathrm{occ}} : \mathrm{Fin}(2Ks) \hookrightarrow \mathrm{Fin}(nq + e_{\mathrm{occ}})$, a family of degree-dependent residual states $\mathrm{degState}_{\mathrm{occ}} : \mathbb{N} \to \mathrm{Qubits}(nq + e_{\mathrm{occ}})$, and a reversible `gates12` circuit $V_{\mathrm{occ}}$ on $nq + e_{\mathrm{occ}}$ qubits of size
--
--   $$
--   |V_{\mathrm{occ}}| \le C_{\mathrm{occ}}\, n\, \bigl(q + \lceil \log_2(nD + 2) \rceil + 1\bigr) + C_{\mathrm{occ}}\, (n + Ks)\, \bigl(\lceil \log_2((K+1)(n+1) + 2) \rceil + 1\bigr)^{K_{\mathrm{occ}}}
--   $$
--
--   such that for every occupation vector $\alpha : \mathrm{Fin}(n) \to \mathbb{N}$ in the active band $K \le \sum_{i=0}^{n-1} \alpha_i \le 2K$, there exists a monotone symbol list $l : \mathrm{Fin}(2K) \to \mathrm{Fin}(n+1)$ containing $\alpha_i$ copies of each particle $i \in \{0, \dots, n-1\}$ and $2K - \sum_i \alpha_i$ blank symbols $n$ for which
--
--   $$
--   V_{\mathrm{occ}} \Bigl(\bigl|\alpha_0, \dots, \alpha_{n-1}\bigr\rangle_{n,q} \otimes |0^{e_{\mathrm{occ}}}\rangle\Bigr) = \mathrm{embedPartAndDeg54}\Bigl(\mathrm{partEmb}_{\mathrm{occ}}, \bigl|\mathrm{particleSym54}(l)\bigr\rangle, \mathrm{degState}_{\mathrm{occ}}\bigl(\textstyle\sum_i \alpha_i\bigr)\Bigr).
--   $$
--
--   This implements Stage A of the second-to-first-quantization conversion in `[LCG26, Section V]`, reversibly computing the total occupation, preparing the sorted NSIL register via trace-recorded bitonic sorting, and uncomputing the original occupation register using a second bitonic sort so that coherence across superpositions over fixed total-degree sectors $\sum_i \alpha_i = k$ is preserved.
--
--   **Formalization Note** Both `flatReg`, `natToBits`, `particleSym54`, and `embedPartAndDeg54` are imported from `Definitions.Def_QuantumLTF_Membership_flatReg` and `Definitions.Def_QuantumLTF_Membership_Supplement_symBand54`.
-- source:
--   Liu, Childs, Gottesman [LCG26], First and second quantization: reversible and quantum circuits (arXiv:2411.04019, Section V); Krivcenko, Nguyen, de Wolf [KNW26], Fast Quantum Algorithms for Learning Linear Threshold Functions (arXiv:2609.40331, Theorem 5.4).

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Circuit
import Definitions.Def_QuantumLTF_Membership_gates12
import Definitions.Def_QuantumLTF_Membership_flatReg
import Definitions.Def_QuantumLTF_Membership_Supplement_padKet
import Definitions.Def_QuantumLTF_Membership_Supplement_symBand54

set_option autoImplicit false

namespace QuantumLTF.Membership.Supplement

open QAlgorithms QuantumLTF.Membership

theorem occupation_to_nsil_54 :
    ∃ (C_occ : ℝ) (K_occ : ℕ), 0 < C_occ ∧
      ∀ (n K D q : ℕ), 1 ≤ n → 1 ≤ K → 2 * K + 1 ≤ D → D ≤ 2 ^ q →
        let s := Nat.clog 2 n + 1
        ∃ (e_occ : ℕ) (partEmb_occ : Fin (2 * K * s) ↪ Fin (n * q + e_occ))
          (degState_occ : ℕ → Qubits (n * q + e_occ))
          (V_occ : Circuit gates12 (n * q + e_occ)),
          ((V_occ.size : ℕ) : ℝ) ≤
            C_occ * n * (q + Nat.clog 2 (n * D + 2) + 1) +
            C_occ * (n + K * s) * (Nat.clog 2 ((K + 1) * (n + 1) + 2) + 1) ^ K_occ ∧
          ∀ (α : Fin n → ℕ), K ≤ ∑ i, α i ∧ ∑ i, α i ≤ 2 * K →
            ∃ (l : Fin (2 * K) → Fin (n + 1)),
              Monotone l ∧
              (∀ i : Fin n, (Finset.univ.filter fun p => l p = ⟨i.1, by omega⟩).card = α i) ∧
              (Finset.univ.filter fun p => l p = ⟨n, Nat.lt_succ_self n⟩).card = 2 * K - ∑ i, α i ∧
              act V_occ.unitary (padKet e_occ (ket (flatReg n q fun i => natToBits q (α i)))) =
                embedPartAndDeg54 partEmb_occ
                  (ket (flatReg (2 * K) s fun p => particleSym54 n s (l p)))
                  (degState_occ (∑ i, α i)) := by sorry

end QuantumLTF.Membership.Supplement
