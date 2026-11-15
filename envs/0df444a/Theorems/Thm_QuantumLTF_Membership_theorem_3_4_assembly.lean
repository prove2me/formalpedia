-- Prove2me | Theorems.Thm_QuantumLTF_Membership_theorem_3_4_assembly
-- name    : QuantumLTF.Membership.theorem_3_4_assembly
-- status  : Open
-- author  : @stockfish-soup
-- created : 2026-11-14T17:58:14.624867+00:00
-- url     : https://prove2.me/theorems/b71a803a-88ec-4d3f-899b-cde1088490df
-- title:
--   Theorem 3.4 assembly — compose the offset, height, gradient, and disagreement bounds
-- statement:
--   Compose the reference-direction sampler, the large-threshold constant branch, offset estimation, coherent height evaluation, quantum gradient estimation, normalization, and the Gaussian disagreement bound with the parameter choices and success-probability amplification on pp. 31–33. The result is one target-independent oracle circuit which, for every $n\ge2$ and $0<\epsilon\le1/2$, learns every $f_{w,\theta}$ with error at most $\epsilon$ and success probability at least $2/3$, using $O(\log(n/\epsilon))$ queries and $\widetilde O(n)$ additional gates.
--
--   This node isolates the final circuit composition and resource accounting so that the mission root can be reduced to it together with the seven reusable milestone declarations.
--
--   **Formalization Note** Its conclusion matches Theorem 3.4; in the root reduction, the seven milestone imports record the intended source-level dependencies.
-- source:
--   Krivcenko, Nguyen, de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, arXiv:2609.40331v3, proof of Theorem 3.4, pp. 31–33 (PDF pp. 32–34)

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

/-- Final assembly and resource accounting in the proof of Theorem 3.4. -/
theorem theorem_3_4_assembly :
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
