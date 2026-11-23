-- Prove2me | Theorems.Thm_QuantumLTF_Membership_localizedAffineBisect_circuit_core
-- name    : QuantumLTF.Membership.localizedAffineBisect_circuit_core
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T03:24:28.972448+00:00
-- url     : https://prove2.me/theorems/4f7683dc-b19d-44c2-aa3d-51765be51c38
-- title:
--   Target-uniform reversible core of localized affine bisection
-- statement:
--   Let $p$ be a reference direction whose coordinates are exact signed fixed-point numbers, and let $\widetilde h$ be an exact fixed-point offset. For every grid precision $b$ and number $q$ of rounds, the coherent localized-bisection computation of Theorem 3.2 has a target-independent reversible implementation over NOT, CNOT, and Toffoli gates.
--
--   The implementation makes at most $2q$ membership-oracle calls, including the reverse bisection pass, and on each computational-basis grid state writes exactly the dyadic output of the affine boundary-bisection tree into a clean fixed-point output register while restoring the work register. There is a universal $C>0$ such that its gate count is at most
--   $$C n\bigl(b+B_p+B_h+\log n+q\bigr)^2(q+1),$$
--   and its output width is at most $C(B_h+q+1)$, where $B_p$ and $B_h$ are the respective input format widths.
--
--   This isolates the reversible address preparation, comparison rounds, and uncomputation from the numerical hypotheses on the unknown target. Target-uniform correctness is the faithful content of pp. 24–26; the geometric estimates in the parent statement are not needed by the circuit construction.
-- source:
--   Krivcenko, Nguyen, de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, arXiv:2609.40331, proof of Theorem 3.2, pp. 24–26 (PDF pp. 25–27), especially Eqs. (40)–(43), reversible comparison rounds, forward/reverse bisection and fixed-point cost accounting.

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Circuit
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QuantumLTF_Membership_affineBoundaryBisect
import Definitions.Def_QuantumLTF_Membership_memOracle
import Definitions.Def_QuantumLTF_Membership_gatesRev
import Definitions.Def_QuantumLTF_Membership_Uncontrolled
import Definitions.Def_QuantumLTF_Membership_ltf
import Definitions.Def_QuantumLTF_Membership_height
import Definitions.Def_QuantumLTF_Membership_rho
import Definitions.Def_QuantumLTF_Membership_IsFp
import Definitions.Def_QuantumLTF_Membership_fpVal
import Definitions.Def_QuantumLTF_Membership_gridVec
import Definitions.Def_QuantumLTF_Membership_regBasis

namespace QuantumLTF.Membership

open QAlgorithms

/-- Syntactic reversible synthesis for Theorem 3.2, pp.24–26 (PDF 25–27).
The circuit is uniform in the target and its cost is expressed using the exact input formats. -/
theorem localizedAffineBisect_circuit_core :
    ∃ C : ℝ, 0 < C ∧ ∀ (n b q : ℕ) (p : EuclideanSpace ℝ (Fin n)) (Bp fp : ℕ),
      (∀ i, IsFp Bp fp (p i)) →
      ∀ (s : ℤ) (htil : ℝ) (Bh fh : ℕ), IsFp Bh fh htil →
        ∃ (ℓ f Vb Vf W : ℕ)
          (c : OracleCircuit gatesRev (fun _ : Fin 1 => n * ℓ + 1) (n * b + Vb + W)),
          Uncontrolled c ∧ c.queryCount 0 ≤ 2 * q ∧
          (c.gateCount : ℝ) ≤ C * n *
            ((b : ℝ) + Bp + Bh + Real.log n + q) ^ 2 * (q + 1) ∧
          (Vb : ℝ) ≤ C * (Bh + q + 1) ∧
          ∀ (w : EuclideanSpace ℝ (Fin n)) (θ : ℝ),
            ∃ Htil : (Fin n → Qubits b) → Qubits Vb,
              (∀ x, act (c.unitary fun _ => memOracle n ℓ f w θ)
                  (ket (regBasis n b Vb W x fun _ => false)) =
                ket (regBasis n b Vb W x (Htil x))) ∧
              ∀ x, fpVal Vb Vf (Htil x) =
                (affineBoundaryBisect p (rho n • gridVec n b x) s q
                  (htil - 1 / 4) (htil + 1 / 4)).run (ltf w θ) := by sorry
