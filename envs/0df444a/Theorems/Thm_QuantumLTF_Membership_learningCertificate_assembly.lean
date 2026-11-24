-- Prove2me | Theorems.Thm_QuantumLTF_Membership_learningCertificate_assembly
-- name    : QuantumLTF.Membership.learningCertificate_assembly
-- status  : Open
-- author  : @Robin Kothari
-- created : 2026-11-24T23:24:52.944514+00:00
-- url     : https://prove2.me/theorems/e7e02e19-6252-41ea-be94-558d1799174d
-- title:
--   Assembly of the coherent learner from its components (helper for Theorem 3.4)
-- statement:
--   This is a proof-engineering helper for `QuantumLTF.Membership.learningCertificate_circuit`: it is the assembly step of the proof of Theorem 3.4, stated for *given* components. From a coherent height-oracle circuit $c_A$ (the conclusion of `uniform_height_circuit` for one parameter choice) and a gradient-estimation circuit $c_3$ (the conclusion of Theorem 3.3 with failure probability $1/6$), it builds the whole learner and shows that it outputs a learning certificate with probability at least $2/3$.
--
--   Let $n,\ell_1,f_1,m,q,\ell,f,b,V_b,W,V_f,m_3,\ell_3,f_3,P\in\mathbb N$ and $\epsilon,\epsilon_g,\eta\in\mathbb R$ with $f_1+q+1\le f$ and $f+m+\ell_1+2\le\ell$. Let $c_A$ be an uncontrolled reversible circuit on $n\ell_1+1+(m+q+2)+(nb+V_b+W)$ qubits and $c_3$ an uncontrolled circuit on $m_3$ qubits with oracle arity $nb+V_b+W$ and output wires $o^{(3)}_i$ of format $(\ell_3,f_3)$. Assume:
--
--   1. $L_\epsilon=2^m$, $2L_\epsilon/2^{q+1}\le\epsilon/100$, $1\le L_\epsilon$, $20\,T_\epsilon\le L_\epsilon$;
--   2. $0\le\epsilon_g\le1$, $2^{-P}\le\epsilon_g$ and $\sqrt n\,(2\epsilon_g)\le\epsilon/(100(L_\epsilon+1))$;
--   3. $c_A$ is block diagonal in its control register $(z_p,s,\tilde h)$ and, under the hypotheses of `uniform_height_circuit` (with $B_h=m+q+2$, $f_h=q+1$), writes an $\eta$-accurate height table $\widetilde H$;
--   4. for every unit $w$, every $p$ with $1/10\le|\langle w,p\rangle|\le3$, every $\eta$-accurate table $\widetilde H$ and every unitary $O_H$ acting as $|x,0\rangle\mapsto|x,\widetilde H(x)\rangle$, the circuit $c_3$ run with oracle $O_H$ outputs, with probability at least $5/6$, values within $\epsilon_g$ of $g=-w/\langle w,p\rangle$ in every coordinate;
--   5. the uniformly random dyadic point $p=\mathrm{addrOf}(z)$, $z\in\{0,1\}^{n\ell_1}$, satisfies $1/10\le|\langle w,p\rangle|\le3$ with probability at least $4/5$ for every unit $w$.
--
--   Then there are $M,\ell_o,f_o$, an uncontrolled oracle circuit $c$ over one- and two-qubit gates on $M$ wires querying the membership oracle of format $(\ell,f)$, and output wires $o_1,\dots,o_n,o_b$ of format $(\ell_o,f_o)$ with $\ell_o\le 2P+(q+2)+(m+q+2)+8$,
--   $$\mathrm{queries}(c)\le 2(q+2)+4+\mathrm{queries}(c_3)\,\mathrm{queries}(c_A),$$
--   and $\mathrm{gates}(c)$ bounded by the explicit expression in the formal statement (linear in $\mathrm{gates}(c_3)+\mathrm{queries}(c_3)\cdot7\,\mathrm{gates}(c_A)$ plus $O(n\ell(q+2)+n\ell_o)$), such that for every unit $w$ and every $\theta$,
--   $$\Pr_{z\sim c|0\rangle}\Bigl[\mathrm{LearningCertificate}\bigl(\epsilon,w,\theta,(\mathrm{readFp}(o_i,z))_i,\mathrm{readFp}(o_b,z)\bigr)\Bigr]\ \ge\ \frac23 .$$
--
--   Together with the parameter choices of Theorems 3.1–3.3 this yields `learningCertificate_circuit` with $O(\log(n/\epsilon))$ queries and $\widetilde O(n)$ gates.
--
--   **Formalization Note** Hypotheses 3–5 are stated verbatim in the shape of the conclusions of `uniform_height_circuit`, `theorem_3_3` (with $\gamma=1/6$) and `uniform_dyadic_reference_direction`, so that they can be discharged by those results.
-- source:
--   Krivcenko, Nguyen, de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, arXiv:2609.40331, proof of Theorem 3.4, pp. 32–34 (PDF pp. 33–35): endpoint test and union bound on p. 32, output representation on p. 33, final offset and gradient estimates on p. 34; components from Theorem 3.1 (p. 21), Theorem 3.2 (p. 23) and Theorem 3.3 (p. 27).

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Circuit
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QuantumLTF_Membership_gates12
import Definitions.Def_QuantumLTF_Membership_gatesRev
import Definitions.Def_QuantumLTF_Membership_Uncontrolled
import Definitions.Def_QuantumLTF_Membership_memOracle
import Definitions.Def_QuantumLTF_Membership_Leps
import Definitions.Def_QuantumLTF_Membership_Teps
import Definitions.Def_QuantumLTF_Membership_addrOf
import Definitions.Def_QuantumLTF_Membership_sgn
import Definitions.Def_QuantumLTF_Membership_fpVal
import Definitions.Def_QuantumLTF_Membership_height
import Definitions.Def_QuantumLTF_Membership_regBasis
import Definitions.Def_QuantumLTF_Membership_rho
import Definitions.Def_QuantumLTF_Membership_gridVec
import Definitions.Def_QuantumLTF_Membership_readFp
import Definitions.Def_QuantumLTF_Membership_LearningCertificate

theorem QuantumLTF.Membership.learningCertificate_assembly :
    ∀ (n ℓ₁ f₁ m q ℓ f b Vb W Vf m₃ ℓo₃ fo₃ P : ℕ) (ε εg η : ℝ),
      f₁ + q + 1 ≤ f → f + m + ℓ₁ + 2 ≤ ℓ →
      ∀ (cA : QAlgorithms.OracleCircuit QuantumLTF.Membership.gatesRev (fun _ : Fin 1 => n * ℓ + 1)
            (n * ℓ₁ + 1 + (m + q + 2) + (n * b + Vb + W)))
        (c₃ : QAlgorithms.OracleCircuit QuantumLTF.Membership.gates12
            (fun _ : Fin 1 => n * b + Vb + W) m₃)
        (oa₃ : Fin n → (Fin ℓo₃ ↪ Fin m₃)),
      QuantumLTF.Membership.Uncontrolled cA → QuantumLTF.Membership.Uncontrolled c₃ →
      QuantumLTF.Membership.Leps ε = 2 ^ m →
      2 * QuantumLTF.Membership.Leps ε / 2 ^ (q + 1) ≤ ε / 100 →
      1 ≤ QuantumLTF.Membership.Leps ε →
      20 * QuantumLTF.Membership.Teps ε ≤ QuantumLTF.Membership.Leps ε →
      0 ≤ εg → εg ≤ 1 → (1 / 2 : ℝ) ^ P ≤ εg →
      Real.sqrt n * (2 * εg) ≤ ε / (100 * (QuantumLTF.Membership.Leps ε + 1)) →
      -- H1's block-diagonality, for this cA
      (∀ w θ (y y' : QAlgorithms.Qubits (n * ℓ₁ + 1 + (m + q + 2) + (n * b + Vb + W))),
        (cA.unitary fun _ => QuantumLTF.Membership.memOracle n ℓ f w θ) y' y ≠ 0 →
        ∀ i : Fin (n * ℓ₁ + 1 + (m + q + 2)),
          y' (Fin.castAdd (n * b + Vb + W) i) = y (Fin.castAdd (n * b + Vb + W) i)) →
      -- H1's action, for this cA, with Bh = m + q + 2 and fh = q + 1
      (∀ w θ (zp : QAlgorithms.Qubits (n * ℓ₁)) (sb : Bool) (hb : QAlgorithms.Qubits (m + q + 2)),
        ‖w‖ = 1 → 1 / 10 ≤ |inner ℝ w (QuantumLTF.Membership.addrOf n ℓ₁ f₁ zp)| →
        |inner ℝ w (QuantumLTF.Membership.addrOf n ℓ₁ f₁ zp)| ≤ 3 →
        (if sb then (1 : ℤ) else -1) =
          QuantumLTF.Membership.sgn (inner ℝ w (QuantumLTF.Membership.addrOf n ℓ₁ f₁ zp)) →
        |QuantumLTF.Membership.fpVal (m + q + 2) (q + 1) hb -
          QuantumLTF.Membership.height w θ (QuantumLTF.Membership.addrOf n ℓ₁ f₁ zp) 0| ≤ ε / 100 →
        ∃ Htil : (Fin n → QAlgorithms.Qubits b) → QAlgorithms.Qubits Vb,
          (∀ x, QAlgorithms.act (cA.unitary fun _ => QuantumLTF.Membership.memOracle n ℓ f w θ)
              (QAlgorithms.ket (Fin.append (Fin.append (Fin.append zp (fun _ : Fin 1 => sb)) hb)
                (QuantumLTF.Membership.regBasis n b Vb W x fun _ => false))) =
            QAlgorithms.ket (Fin.append (Fin.append (Fin.append zp (fun _ : Fin 1 => sb)) hb)
                (QuantumLTF.Membership.regBasis n b Vb W x (Htil x)))) ∧
          ∀ x, |QuantumLTF.Membership.fpVal Vb Vf (Htil x) -
            QuantumLTF.Membership.height w θ (QuantumLTF.Membership.addrOf n ℓ₁ f₁ zp)
              (QuantumLTF.Membership.rho n • QuantumLTF.Membership.gridVec n b x)| ≤ η) →
      -- theorem_3_3's conclusion for this c₃ (γ = 1/6)
      (∀ (w p : EuclideanSpace ℝ (Fin n)) (θ : ℝ), ‖w‖ = 1 → 1 / 10 ≤ |inner ℝ w p| →
        |inner ℝ w p| ≤ 3 → ∀ Htil : (Fin n → QAlgorithms.Qubits b) → QAlgorithms.Qubits Vb,
        (∀ x, |QuantumLTF.Membership.fpVal Vb Vf (Htil x) - QuantumLTF.Membership.height w θ p
            (QuantumLTF.Membership.rho n • QuantumLTF.Membership.gridVec n b x)| ≤ η) →
        ∀ OH : Matrix (QAlgorithms.Qubits (n * b + Vb + W)) (QAlgorithms.Qubits (n * b + Vb + W)) ℂ,
          OH ∈ Matrix.unitaryGroup (QAlgorithms.Qubits (n * b + Vb + W)) ℂ →
          (∀ x, QAlgorithms.act OH (QAlgorithms.ket (QuantumLTF.Membership.regBasis n b Vb W x
              fun _ => false)) = QAlgorithms.ket (QuantumLTF.Membership.regBasis n b Vb W x (Htil x))) →
          open Classical in
          QAlgorithms.probEvent (QAlgorithms.act (c₃.unitary fun _ => OH) (QAlgorithms.zeroKet m₃))
            (fun z => ∀ i, |QuantumLTF.Membership.readFp (oa₃ i) fo₃ z - (-(w i) / inner ℝ w p)| ≤ εg)
            ≥ 5 / 6) →
      -- uniform_dyadic_reference_direction's conclusion for (ℓ₁, f₁)
      (∀ w : EuclideanSpace ℝ (Fin n), ‖w‖ = 1 →
        ((PMF.uniformOfFintype (QAlgorithms.Qubits (n * ℓ₁))).toOuterMeasure
          {z | 1 / 10 ≤ |inner ℝ w (QuantumLTF.Membership.addrOf n ℓ₁ f₁ z)| ∧
            |inner ℝ w (QuantumLTF.Membership.addrOf n ℓ₁ f₁ z)| ≤ 3}).toReal ≥ 4 / 5) →
      ∃ (M ℓo fo : ℕ) (c : QAlgorithms.OracleCircuit QuantumLTF.Membership.gates12
          (fun _ : Fin 1 => n * ℓ + 1) M) (oa : Fin n → (Fin ℓo ↪ Fin M)) (ob : Fin ℓo ↪ Fin M),
        QuantumLTF.Membership.Uncontrolled c ∧
        ℓo ≤ 2 * P + (q + 2) + (m + q + 2) + 8 ∧
        c.queryCount 0 ≤ 2 * (q + 2) + 4 + c₃.queryCount 0 * cA.queryCount 0 ∧
        c.gateCount ≤ n * ℓ₁ + 1200 * (n * ℓ + m + q + 2) * (q + 2) +
          (20 * (2 + 2 * (n * (12 * ℓ)) + 2 * (n * ℓ + 1) + 1) + 2) +
          (c₃.gateCount + c₃.queryCount 0 * (7 * cA.gateCount)) + 10 * (2 + n * ℓo) +
          10 * (3 + n * (15 * ℓo) + 18 * ℓo + (n + 1) * ℓo) ∧
        ∀ w : EuclideanSpace ℝ (Fin n), ‖w‖ = 1 → ∀ θ : ℝ,
          open Classical in
          QAlgorithms.probEvent
            (QAlgorithms.act (c.unitary fun _ => QuantumLTF.Membership.memOracle n ℓ f w θ)
              (QAlgorithms.zeroKet M))
            (fun z => QuantumLTF.Membership.LearningCertificate ε w θ
              (WithLp.toLp 2 fun i => QuantumLTF.Membership.readFp (oa i) fo z)
              (QuantumLTF.Membership.readFp ob fo z)) ≥ 2 / 3 := by sorry
