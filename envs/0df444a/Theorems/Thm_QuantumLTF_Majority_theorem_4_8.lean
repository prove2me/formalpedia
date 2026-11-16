-- Prove2me | Theorems.Thm_QuantumLTF_Majority_theorem_4_8
-- name    : QuantumLTF.Majority.theorem_4_8
-- status  : Open
-- author  : @stockfish-soup
-- created : 2026-11-15T20:35:49.188449+00:00
-- url     : https://prove2.me/theorems/2926b6f4-14d6-4810-a050-52ae1952a7b2
-- title:
--   Theorem 4.8 — exact Hamming-weight counter
-- statement:
--   An exact reversible Hamming-weight counter maps $|T\rangle|0^\ell\rangle$ to $|T\rangle||T|\rangle$, where $\ell=\lceil\log_2(n+1)\rceil$. It uses $O(n\log n)$ one- and two-qubit gates and has parallel depth $O(\log n)$.
-- source:
--   Krivcenko, Nguyen, de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, STOC 2027 submission #347, Theorem 4.8, p. 52 (PDF p. 53), citing ZYN26 Theorem 1.

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QAlgorithms_Defs_Circuit
import Definitions.Def_QuantumLTF_Membership_gates12
import Definitions.Def_QuantumLTF_Sections45_Model

namespace QuantumLTF.Majority

open QAlgorithms QuantumLTF.Membership

theorem theorem_4_8 :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
      let ℓ := Nat.clog 2 (n + 1)
      ∃ (c : Circuit gates12 (n + ℓ)) (d : ℕ),
        (c.size : ℝ) ≤ C * n * Real.log (n + 1) ∧
        (d : ℝ) ≤ C * Real.log (n + 1) ∧ HasDepth c d ∧
        ∀ T : Qubits n, ∃ v : Qubits ℓ, bitsToNat v = (Finset.univ.filter fun i => T i).card ∧
          act c.unitary (ket (Fin.append T fun _ => false)) = ket (Fin.append T v) := by sorry

end QuantumLTF.Majority
