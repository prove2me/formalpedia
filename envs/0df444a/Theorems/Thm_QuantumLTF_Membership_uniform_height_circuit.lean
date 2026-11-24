-- Prove2me | Theorems.Thm_QuantumLTF_Membership_uniform_height_circuit
-- name    : QuantumLTF.Membership.uniform_height_circuit
-- status  : Proved
-- author  : @Robin Kothari
-- created : 2026-11-24T22:59:17.512257+00:00
-- url     : https://prove2.me/theorems/27f613f3-e3f2-4af2-ae37-b98408409167
-- title:
--   Coherent local height oracle, uniform in the reference point (helper for Theorem 3.4)
-- statement:
--   This is a proof-engineering helper for `QuantumLTF.Membership.learningCertificate_circuit`, isolating the coherent height oracle $O_H$ that the proof of Theorem 3.4 feeds to the gradient estimator of Theorem 3.3. It packages the local bisection of Theorem 3.2 as one reversible circuit that works *uniformly* in the reference point $p$ held in a quantum register.
--
--   Fix constants $C_1,C_2\ge0$. There is a constant $C>0$ with the following property. Let $n\ge2$, $0<\epsilon\le1/2$, $0<\eta<1/8$, and let $b,\ell_1,f_1,B_h,f_h\in\mathbb N$ satisfy $\ell_1\le C_1\log n$, $f_1\le\ell_1$, $B_h\le C_2\log(1/\epsilon)$ and $f_h\le B_h$. Then there are register sizes $V_b,V_f,F,D$ with
--   $$V_b\le C\bigl(\log\tfrac1\epsilon+\log\tfrac1\eta\bigr),\qquad F,\,D\le C\bigl(\log n+\log\tfrac1\epsilon+\log\tfrac1\eta+b\bigr),$$
--   such that for every query format $(\ell,f)$ with $F\le f$ and $f+D\le\ell$ there are $W\in\mathbb N$ and an uncontrolled reversible circuit $c$ (gates NOT, CNOT, Toffoli) on $n\ell_1+1+B_h+(nb+V_b+W)$ qubits, querying the membership oracle $O_{w,\theta}$ of $f_{w,\theta}(x)=\operatorname{sgn}(\langle w,x\rangle-\theta)$ on the fixed-point grid of format $(\ell,f)$, with:
--
--   1. at most $C\log(1/\eta)$ oracle queries and at most $C\,n\,(b+\log n+\log\frac1\epsilon+\log\frac1\eta)^2\log\frac1\eta+C\,n\,\ell\log\frac1\eta$ gates;
--   2. for all $w,\theta$, the circuit never changes the control register (the first $n\ell_1+1+B_h$ qubits holding $z_p$, a sign bit $s$ and an offset estimate $\tilde h$): every nonzero matrix entry connects basis states that agree there;
--   3. for every unit vector $w$, every $\theta$, and basis values $z_p,s,\tilde h$ such that $p=\mathrm{addrOf}(z_p)$ satisfies $1/10\le|\langle w,p\rangle|\le3$, $s$ encodes $\operatorname{sgn}\langle w,p\rangle$, and $|\mathrm{fpVal}(\tilde h)-h_p(0)|\le\epsilon/100$ where $h_p(z)=(\theta-\langle w,z\rangle)/\langle w,p\rangle$, there is $\widetilde H:(G_b)^n\to\{0,1\}^{V_b}$ with
--   $$c\,|z_p,s,\tilde h\rangle|x\rangle|0\rangle|0^W\rangle=|z_p,s,\tilde h\rangle|x\rangle|\widetilde H(x)\rangle|0^W\rangle,\qquad \bigl|\mathrm{fpVal}_{V_f}(\widetilde H(x))-h_p(\rho\,x)\bigr|\le\eta$$
--   for every grid point $x$ (written as $b$ bits per coordinate, $\rho=\rho_n$ the grid scale).
--
--   In the proof of Theorem 3.4 this circuit, controlled by the outputs of the offset search (Theorem 3.1), is the oracle $O_H$ required by Theorem 3.3.
--
--   **Formalization Note** The register is laid out as `Fin.append (Fin.append (Fin.append zp s) hb) (regBasis n b Vb W x v)`; the size $W$ of the scratch block may depend on $(\ell,f)$.
-- source:
--   Krivcenko, Nguyen, de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, arXiv:2609.40331, proof of Theorem 3.4, pp. 32–34 (PDF pp. 33–35): the height oracle O_H required by Theorem 3.3 (p. 27, PDF p. 28), implemented by the local bisection of Theorem 3.2 (p. 23, PDF p. 24).

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Circuit
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QuantumLTF_Membership_memOracle
import Definitions.Def_QuantumLTF_Membership_gatesRev
import Definitions.Def_QuantumLTF_Membership_Uncontrolled
import Definitions.Def_QuantumLTF_Membership_fpVal
import Definitions.Def_QuantumLTF_Membership_addrOf
import Definitions.Def_QuantumLTF_Membership_regBasis
import Definitions.Def_QuantumLTF_Membership_gridVec
import Definitions.Def_QuantumLTF_Membership_rho
import Definitions.Def_QuantumLTF_Membership_height
import Definitions.Def_QuantumLTF_Membership_sgn

namespace QuantumLTF.Membership

open QAlgorithms

theorem uniform_height_circuit (C₁ C₂ : ℝ) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 2 ≤ n → ∀ ε η : ℝ, 0 < ε → ε ≤ 1 / 2 → 0 < η → η < 1 / 8 →
      ∀ (b ℓ₁ f₁ Bh fh : ℕ), (ℓ₁ : ℝ) ≤ C₁ * Real.log n → f₁ ≤ ℓ₁ →
        (Bh : ℝ) ≤ C₂ * Real.log (1 / ε) → fh ≤ Bh →
      ∃ (Vb Vf F D : ℕ),
        (Vb : ℝ) ≤ C * (Real.log (1 / ε) + Real.log (1 / η)) ∧
        (F : ℝ) ≤ C * (Real.log n + Real.log (1 / ε) + Real.log (1 / η) + b) ∧
        (D : ℝ) ≤ C * (Real.log n + Real.log (1 / ε) + Real.log (1 / η) + b) ∧
        ∀ ℓ f : ℕ, F ≤ f → f + D ≤ ℓ →
        ∃ (W : ℕ) (c : OracleCircuit gatesRev (fun _ : Fin 1 => n * ℓ + 1)
            (n * ℓ₁ + 1 + Bh + (n * b + Vb + W))),
          Uncontrolled c ∧
          (c.queryCount 0 : ℝ) ≤ C * Real.log (1 / η) ∧
          (c.gateCount : ℝ) ≤ C * n * (b + Real.log n + Real.log (1 / ε) + Real.log (1 / η)) ^ 2 *
              Real.log (1 / η) + C * n * ℓ * Real.log (1 / η) ∧
          (∀ (w : EuclideanSpace ℝ (Fin n)) (θ : ℝ)
              (y y' : Qubits (n * ℓ₁ + 1 + Bh + (n * b + Vb + W))),
            (c.unitary fun _ => memOracle n ℓ f w θ) y' y ≠ 0 →
            ∀ i : Fin (n * ℓ₁ + 1 + Bh),
              y' (Fin.castAdd (n * b + Vb + W) i) = y (Fin.castAdd (n * b + Vb + W) i)) ∧
          ∀ (w : EuclideanSpace ℝ (Fin n)) (θ : ℝ) (zp : Qubits (n * ℓ₁)) (sb : Bool)
            (hb : Qubits Bh), ‖w‖ = 1 →
            1 / 10 ≤ |inner ℝ w (addrOf n ℓ₁ f₁ zp)| → |inner ℝ w (addrOf n ℓ₁ f₁ zp)| ≤ 3 →
            (if sb then (1 : ℤ) else -1) = sgn (inner ℝ w (addrOf n ℓ₁ f₁ zp)) →
            |fpVal Bh fh hb - height w θ (addrOf n ℓ₁ f₁ zp) 0| ≤ ε / 100 →
            ∃ Htil : (Fin n → Qubits b) → Qubits Vb,
              (∀ x, act (c.unitary fun _ => memOracle n ℓ f w θ)
                  (ket (Fin.append (Fin.append (Fin.append zp (fun _ : Fin 1 => sb)) hb)
                    (regBasis n b Vb W x fun _ => false))) =
                ket (Fin.append (Fin.append (Fin.append zp (fun _ : Fin 1 => sb)) hb)
                    (regBasis n b Vb W x (Htil x)))) ∧
              ∀ x, |fpVal Vb Vf (Htil x) -
                height w θ (addrOf n ℓ₁ f₁ zp) (rho n • gridVec n b x)| ≤ η := by sorry

end QuantumLTF.Membership
