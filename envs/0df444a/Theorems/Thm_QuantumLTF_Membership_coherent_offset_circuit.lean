-- Prove2me | Theorems.Thm_QuantumLTF_Membership_coherent_offset_circuit
-- name    : QuantumLTF.Membership.coherent_offset_circuit
-- status  : Proved
-- author  : @Robin Kothari
-- created : 2026-11-24T23:14:38.941406+00:00
-- url     : https://prove2.me/theorems/f4ebe736-01ac-4651-a4f0-ce0f30289d8d
-- title:
--   Coherent offset estimation (Theorem 3.1), uniform in the reference point (helper for Theorem 3.4)
-- statement:
--   This is a proof-engineering helper for `QuantumLTF.Membership.learningCertificate_circuit`: the offset search of Theorem 3.1 implemented as one coherent circuit that is *uniform in the reference point* $p$, which is held in a quantum register, with exact semantics on basis states.
--
--   Let $n,\ell_1,f_1,m,q,\ell,f\in\mathbb N$ with $f_1+q+1\le f$ and $f+m+\ell_1+2\le\ell$. Then there are a number $M$ of wires, an uncontrolled oracle circuit $c$ over one- and two-qubit gates on $M$ wires querying the membership oracle $O_{w,\theta}$ (the LTF $f_{w,\theta}(x)=\operatorname{sgn}(\langle w,x\rangle-\theta)$ restricted to the fixed-point grid of format $(\ell,f)$), an embedding $\mathrm{pin}$ of the $n\ell_1$ input wires of $p$, a sign wire $\mathrm{sw}$ and an embedding $\mathrm{hw}$ of $m+q+2$ offset wires, pairwise disjoint, such that:
--
--   1. $c$ makes at most $2(q+2)$ queries and uses at most $1200\,(n\ell+m+q+2)(q+2)$ gates;
--   2. for all $w,\theta$ and every basis state $z$ that vanishes outside $\mathrm{pin}$, $c$ maps $|z\rangle$ to a basis state $|z'\rangle$ that agrees with $z$ outside $\{\mathrm{sw}\}\cup\mathrm{hw}$, and, writing $p=\mathrm{addrOf}(z\circ\mathrm{pin})$ and $(s,\tilde h)$ for the output of the strict boundary-search tree $T_{p,L,q}$ with $L=2^m$ run on $f_{w,\theta}$,
--   $$z'(\mathrm{sw})=[\,s=1\,],\qquad \mathrm{fpVal}_{m+q+2,\;q+1}\bigl(z'\circ\mathrm{hw}\bigr)=\tilde h .$$
--
--   Combined with the analysis of the search tree (`boundarySearchTreeStrict_run`, `orientedBisectValue_error`) this gives, coherently over all $p$, the sign $\operatorname{sgn}\langle w,p\rangle$ and the estimate $\tilde h_p(0)$ used in the proof of Theorem 3.4.
--
--   **Formalization Note** Basis states are the vectors `Pi.single z 1`; the format conditions guarantee that the queried points $t\,p$ of the tree are exactly representable.
-- source:
--   Krivcenko, Nguyen, de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, arXiv:2609.40331, proof of Theorem 3.4, pp. 32–34 (PDF pp. 33–35): coherent use of the offset search of Theorem 3.1, Eq. (27), p. 21 (PDF p. 22), for a superposition of reference points p.

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Circuit
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QuantumLTF_Membership_gates12
import Definitions.Def_QuantumLTF_Membership_Uncontrolled
import Definitions.Def_QuantumLTF_Membership_memOracle
import Definitions.Def_QuantumLTF_Membership_boundarySearchTreeStrict
import Definitions.Def_QuantumLTF_Membership_addrOf
import Definitions.Def_QuantumLTF_Membership_ltf
import Definitions.Def_QuantumLTF_Membership_fpVal

theorem QuantumLTF.Membership.coherent_offset_circuit :
    ∀ (n ℓ₁ f₁ m q ℓ f : ℕ), f₁ + q + 1 ≤ f → f + m + ℓ₁ + 2 ≤ ℓ →
      ∃ (M : ℕ) (c : QAlgorithms.OracleCircuit QuantumLTF.Membership.gates12
          (fun _ : Fin 1 => n * ℓ + 1) M)
        (pin : Fin (n * ℓ₁) ↪ Fin M) (sw : Fin M) (hw : Fin (m + q + 2) ↪ Fin M),
        QuantumLTF.Membership.Uncontrolled c ∧
        c.queryCount 0 ≤ 2 * (q + 2) ∧
        c.gateCount ≤ 1200 * (n * ℓ + m + q + 2) * (q + 2) ∧
        (∀ i, pin i ≠ sw) ∧ (∀ i j, pin i ≠ hw j) ∧ (∀ j, hw j ≠ sw) ∧
        ∀ (w : EuclideanSpace ℝ (Fin n)) (θ : ℝ) (z : QAlgorithms.Qubits M),
          (∀ v, v ∉ Set.range pin → z v = false) →
          ∃ z' : QAlgorithms.Qubits M,
            (c.unitary fun _ => QuantumLTF.Membership.memOracle n ℓ f w θ).mulVec
                (Pi.single z 1) = Pi.single z' 1 ∧
            (∀ v, v ≠ sw → v ∉ Set.range hw → z' v = z v) ∧
            z' sw = decide (((QuantumLTF.Membership.boundarySearchTreeStrict
              (QuantumLTF.Membership.addrOf n ℓ₁ f₁ (z ∘ pin)) ((2 : ℝ) ^ m) q).run
              (QuantumLTF.Membership.ltf w θ)).1 = 1) ∧
            QuantumLTF.Membership.fpVal (m + q + 2) (q + 1) (z' ∘ hw) =
              ((QuantumLTF.Membership.boundarySearchTreeStrict
                (QuantumLTF.Membership.addrOf n ℓ₁ f₁ (z ∘ pin)) ((2 : ℝ) ^ m) q).run
                (QuantumLTF.Membership.ltf w θ)).2 := by sorry
