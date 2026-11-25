-- Prove2me | Theorems.Thm_QuantumLTF_Membership_Supplement_nsil_symmetrize_54
-- name    : QuantumLTF.Membership.Supplement.nsil_symmetrize_54
-- status  : Proved
-- author  : @Robin Kothari
-- created : 2026-11-25T03:11:24.179715+00:00
-- url     : https://prove2.me/theorems/97ffba61-5e64-4157-98ff-b1f64c94ae6d
-- title:
--   Exact Stage B NSIL symmetrization circuit in $\mathrm{gates12}$
-- statement:
--   There exist universal constants $C_{\mathrm{sym}} > 0$ and $K_{\mathrm{sym}} \in \mathbb{N}$ such that for every $n \ge 1$ and $K \ge 1$ (with $s = \lceil \log_2 n \rceil + 1$), there is an ancilla count $e_{\mathrm{sym}}$ and a `gates12` circuit $V_{\mathrm{sym}}$ on $2Ks + e_{\mathrm{sym}}$ qubits satisfying
--
--   $$
--   |V_{\mathrm{sym}}| \le C_{\mathrm{sym}}\, (Ks)\, \bigl(\lceil \log_2((K+1)(n+1)+2) \rceil + 1\bigr)^{K_{\mathrm{sym}}}
--   $$
--
--   that reversibly maps every sorted $2K$-particle NSIL computational basis state $|l_0, \dots, l_{2K-1}\rangle$ having $\alpha_i$ copies of particle $i \in \{0,\dots,n-1\}$ and $2K - \sum_i \alpha_i$ blank symbols $\bot$ (for $K \le \sum_i \alpha_i \le 2K$) directly to the exact multinomial Dicke/symmetric state
--
--   $$
--   V_{\mathrm{sym}} \bigl(|\mathrm{particleSym}(l)\rangle \otimes |0^{e_{\mathrm{sym}}}\rangle\bigr) = |\mathrm{multinomKet54}(n, s, K, \alpha)\rangle \otimes |0^{e_{\mathrm{sym}}}\rangle.
--   $$
--
--   This implements Stage B of the second-to-first-quantization reduction in `[LCG26]` Equations (655)–(701) using bitonic trace sorting (`bitonic_routing_54`), uniform permutation preparation (`alonso_schott_sil_54`), and in-place Equation (693) stabilizer uncomputation (`harm_bucket_hl_54`), preserving coherence across superposed occupation-number sectors for `theorem_5_4`.
--
--   **Formalization Note** Particle encodings `particleSym54` and target state `multinomKet54` are imported from `Definitions.Def_QuantumLTF_Membership_Supplement_symBand54`.
-- source:
--   Liu, Childs, Gottesman [LCG26], First and second quantization: reversible and quantum circuits (arXiv:2411.04019, Section IV, Equations 655–701); Krivcenko, Nguyen, de Wolf [KNW26] (arXiv:2609.40331, Theorem 5.4).

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QAlgorithms_Defs_Circuit
import Definitions.Def_QuantumLTF_Membership_gates12
import Definitions.Def_QuantumLTF_Membership_flatReg
import Definitions.Def_QuantumLTF_Membership_splitReg
import Definitions.Def_QuantumLTF_Membership_Supplement_padKet
import Definitions.Def_QuantumLTF_Membership_Supplement_symBand54

set_option autoImplicit false

namespace QuantumLTF.Membership.Supplement

open QAlgorithms QuantumLTF.Membership

theorem nsil_symmetrize_54 :
    ∃ (C_sym : ℝ), 0 < C_sym ∧ ∃ (K_sym : ℕ),
      ∀ (n K : ℕ), 1 ≤ n → 1 ≤ K →
        let s := Nat.clog 2 n + 1
        ∃ (e_sym : ℕ) (V_sym : Circuit gates12 (2 * K * s + e_sym)),
          ((V_sym.size : ℕ) : ℝ) ≤
            C_sym * ((K * s : ℕ) : ℝ) *
              ((Nat.clog 2 ((K + 1) * (n + 1) + 2) + 1 : ℕ) : ℝ) ^ K_sym ∧
          ∀ (α : Fin n → ℕ) (hk : K ≤ ∑ i, α i ∧ ∑ i, α i ≤ 2 * K)
            (l : Fin (2 * K) → Fin (n + 1)),
            Monotone l →
            (∀ i : Fin n, (Finset.univ.filter fun p => l p = ⟨i.1, by omega⟩).card = α i) →
            (Finset.univ.filter fun p => l p = ⟨n, Nat.lt_succ_self n⟩).card = 2 * K - ∑ i, α i →
            act V_sym.unitary (padKet e_sym (ket (flatReg (2 * K) s fun p => particleSym54 n s (l p)))) =
              padKet e_sym (multinomKet54 n s K α hk) := by sorry

end QuantumLTF.Membership.Supplement
