-- Prove2me | Theorems.Thm_QuantumLTF_Membership_learningCertificate_circuit
-- name    : QuantumLTF.Membership.learningCertificate_circuit
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T03:57:43.860044+00:00
-- url     : https://prove2.me/theorems/b46352ac-e6b9-4476-ac9c-37b505ab99bb
-- title:
--   Coherent learner outputs an analytic learning certificate
-- statement:
--   The coherent circuit implementing the algorithm in the proof of Theorem 3.4, with the advertised $O(\log(n/\epsilon))$ query and $\widetilde O(n)$ gate bounds, outputs fixed-point parameters $(a,b)$ carrying a *learning certificate* with probability at least $2/3$. In the nearly constant branch, the certificate says that $a$ gives the constant labeling $f_{w,\theta}(0)$ and $|\theta|\ge L_\epsilon$. Otherwise it contains a sign $s\in\{\pm1\}$, offset estimates $h,\widetilde h$, and directions $g,\widetilde g$ satisfying the source's exact identities $w=-sg/\|g\|$, $\theta=sh/\|g\|$, together with $1/3\le\|g\|\le10$, $|h|\le L_\epsilon$, $|\widetilde h-h|\le\epsilon/100$, and $\|\widetilde g-g\|\le\epsilon/(100(L_\epsilon+1))$. The nonconstant output is the raw, unnormalized pair $a=-s\widetilde g$, $b=s\widetilde h$.
-- source:
--   Krivcenko, Nguyen, de Wolf, *Fast Quantum Algorithms for Learning Linear Threshold Functions*, arXiv:2609.40331, proof of Theorem 3.4, pp. 32–34 (PDF pp. 33–35): endpoint test and union bound on p. 32, output representation on p. 33, final offset and gradient estimates on p. 34. The certificate records precisely the successful-run hypotheses used in Eqs. (64)–(71), while retaining the circuit-level query and gate bounds of Theorem 3.4 on p. 31.

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Circuit
import Definitions.Def_QuantumLTF_Membership_ltf
import Definitions.Def_QuantumLTF_Membership_disagree
import Definitions.Def_QuantumLTF_Membership_memOracle
import Definitions.Def_QuantumLTF_Membership_gates12
import Definitions.Def_QuantumLTF_Membership_Uncontrolled
import Definitions.Def_QuantumLTF_Membership_readFp
import Definitions.Def_QuantumLTF_Membership_LearningCertificate

theorem QuantumLTF.Membership.learningCertificate_circuit :
    ∃ (C : ℝ) (K : ℕ), 0 < C ∧ ∀ n : ℕ, 2 ≤ n → ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 →
      ∃ (ℓ f m ℓo fo : ℕ)
        (c : QAlgorithms.OracleCircuit QuantumLTF.Membership.gates12
          (fun _ : Fin 1 => n * ℓ + 1) m)
        (oa : Fin n → (Fin ℓo ↪ Fin m)) (ob : Fin ℓo ↪ Fin m),
        QuantumLTF.Membership.Uncontrolled c ∧
        (c.queryCount 0 : ℝ) ≤ C * Real.log (n / ε) ∧
        (c.gateCount : ℝ) ≤ C * n * (Real.log (n / ε)) ^ K ∧
        ∀ w : EuclideanSpace ℝ (Fin n), ‖w‖ = 1 → ∀ θ : ℝ,
          open Classical in
          QAlgorithms.probEvent
            (QAlgorithms.act (c.unitary fun _ => QuantumLTF.Membership.memOracle n ℓ f w θ)
              (QAlgorithms.zeroKet m))
            (fun z => QuantumLTF.Membership.LearningCertificate ε w θ
              (WithLp.toLp 2 fun i => QuantumLTF.Membership.readFp (oa i) fo z)
              (QuantumLTF.Membership.readFp ob fo z)) ≥ 2 / 3 := by sorry
