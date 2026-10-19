-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier18_P14_passiveFockExtension
-- name    : QAlgorithms.Papers.Independent.Frontier18.P14.passiveFockExtension
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T09:04:42.424493+00:00
-- url     : https://prove2.me/theorems/c3cf1a5b-b1e9-46d3-87af-a9986789f6f9
-- title:
--   Continuous passive Fock isometry and Weyl covariance
-- statement:
--   Let $\mathcal H=\ell^2(\mathbb N^2)$ and let $B$ be any unitary two-mode beam matrix. Let $v_{mn}(B)$ be the normalized occupation polynomial obtained by substituting $B$ into the creation operators of $|m,n\rangle$. Define each output coefficient by the finite total-number-sector sum
--
--   $$(V_B\psi)_{pq}=\sum_{m=0}^{p+q}\psi_{m,p+q-m}\,[v_{m,p+q-m}(B)]_{pq}.$$
--
--   For every $\psi\in\mathcal H$ these coefficients are square summable. They define a continuous complex linear isometry equivalence $V_B$, with $V_B|m,n\rangle=v_{mn}(B)$, $V_B|0,0\rangle=|0,0\rangle$, $\|V_B\psi\|=\|\psi\|$, and inverse $V_{B^\dagger}$. Rectangular occupation truncations converge in Hilbert norm.
--
--   With the explicit occupation coefficients of $D(z)=\exp(z a^\dagger-\overline z a)$, the two-mode displacement $D(z_1)\otimes D(z_2)$ is likewise a full-space isometry equivalence, has inverse at $-z$, and satisfies
--
--   $$V_BD(z)\psi=D(Bz)V_B\psi.$$
--
--   For every normalized input $\psi$, its rank-one operator and both reduced operators are genuine density operators. Writing $\rho_j$ for partial trace retaining output $j$, both reduced-state covariance laws hold:
--
--   $$\rho_j(V_BD(z)\psi)=D((Bz)_j)\rho_j(V_B\psi)D((Bz)_j)^\dagger,\qquad j=1,2.$$
--
--   All series used in these formulas have summability conclusions. The rank-one operators of rectangular truncations, and both of their partial traces, converge in trace norm. No absolute summability of arbitrary input coefficient products and no energy cutoff are assumed. This specifies the mathematical full-space meaning of the paper's passive evolution and supplies the requested supporting interface.
-- source:
--   Quantum Physics of Simple Optical Instruments, arXiv:quant-ph/0305007v2, PDF p. 20, §§3.2,4.2–4.3: passive evolution on full two-mode Fock space

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P14

noncomputable section

open scoped Matrix ComplexConjugate

open Filter

attribute [local instance] Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Frontier18.P14

open QAlgorithms.Papers.Independent.Dependency50.P34 (fockKet)

/-- PDF pp.10,20–21, (3.9),(4.12),(4.18)–(4.20): the concrete sector
extension is a continuous linear isometry equivalence on all l² inputs, fixes
vacuum, and has inverse given by the adjoint beam matrix. Rectangular occupation
truncations converge in Hilbert norm and their rank-one and reduced operators
converge in trace norm. Full Weyl displacement covariance includes both reduced
outputs on arbitrary normalized inputs, without any l¹ coefficient assumption. -/
theorem passiveFockExtension (B : Matrix (Fin 2) (Fin 2) ℂ)
    (hB : B ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    (∀ psi : Fock, Memℓp (passiveCoefficients B psi) 2) ∧
    (∃ U : Fock ≃ₗᵢ[ℂ] Fock, ∀ psi, U psi = passiveApply B psi) ∧
    (∀ m n, passiveApply B (fockKet m n) = occupationOutput B m n) ∧
    passiveApply B (fockKet 0 0) = fockKet 0 0 ∧
    (∀ psi : Fock, ‖passiveApply B psi‖ = ‖psi‖ ∧
      passiveApply B.conjTranspose (passiveApply B psi) = psi ∧
      passiveApply B (passiveApply B.conjTranspose psi) = psi ∧
      Tendsto (fun MN : ℕ × ℕ =>
        ∑ m ∈ Finset.range MN.1, ∑ n ∈ Finset.range MN.2,
          psi (m, n) • occupationOutput B m n)
        atTop (nhds (passiveApply B psi))) ∧
    (∀ (z : Fin 2 → ℂ) (psi : Fock),
      (∀ pq : ℕ × ℕ, Summable (fun mn : ℕ × ℕ =>
        displacementEntry (z 0) pq.1 mn.1 * displacementEntry (z 1) pq.2 mn.2 * psi mn)) ∧
      Memℓp (displacedCoefficients z psi) 2) ∧
    (∀ z : Fin 2 → ℂ,
      ∃ D : Fock ≃ₗᵢ[ℂ] Fock, ∀ psi, D psi = displace z psi) ∧
    (∀ (z : Fin 2 → ℂ) (psi : Fock),
      displace (-z) (displace z psi) = psi ∧
      passiveApply B (displace z psi) =
        displace (B.mulVec z) (passiveApply B psi)) ∧
    (∀ (psi : Fock) (i j : ℕ),
      Summable (fun k : ℕ => psi (i, k) * star (psi (j, k))) ∧
      Summable (fun k : ℕ => psi (k, i) * star (psi (k, j)))) ∧
    (∀ (psi : Fock) (hpsi : ‖psi‖ = 1),
      QAlgorithms.Papers.Independent.Dependency50.P33.IsDensity (pureOperator psi) ∧
      QAlgorithms.Papers.Independent.Dependency50.P33.IsDensity (fockReducedFirst psi) ∧
      QAlgorithms.Papers.Independent.Dependency50.P33.IsDensity (reducedSecond psi) ∧
      (∀ z : Fin 2 → ℂ,
        fockReducedFirst (passiveApply B (displace z psi)) =
          displacedOperator (B.mulVec z 0) (fockReducedFirst (passiveApply B psi)) ∧
        reducedSecond (passiveApply B (displace z psi)) =
          displacedOperator (B.mulVec z 1) (reducedSecond (passiveApply B psi)) ∧
        (∀ i j : ℕ,
          Summable (fun mn : ℕ × ℕ => displacementEntry (B.mulVec z 0) i mn.1 *
            fockReducedFirst (passiveApply B psi) mn.1 mn.2 *
              star (displacementEntry (B.mulVec z 0) j mn.2)) ∧
          Summable (fun mn : ℕ × ℕ => displacementEntry (B.mulVec z 1) i mn.1 *
            reducedSecond (passiveApply B psi) mn.1 mn.2 *
              star (displacementEntry (B.mulVec z 1) j mn.2)))) ∧
      Tendsto (fun MN : ℕ × ℕ =>
        QAlgorithms.Papers.Independent.Dependency50.P33.traceSize
          (pureOperator (rectangularOutput B psi MN) - pureOperator (passiveApply B psi)))
        atTop (nhds 0) ∧
      Tendsto (fun MN : ℕ × ℕ =>
        QAlgorithms.Papers.Independent.Dependency50.P33.traceSize
          (fockReducedFirst (rectangularOutput B psi MN) - fockReducedFirst (passiveApply B psi)))
        atTop (nhds 0) ∧
      Tendsto (fun MN : ℕ × ℕ =>
        QAlgorithms.Papers.Independent.Dependency50.P33.traceSize
          (reducedSecond (rectangularOutput B psi MN) - reducedSecond (passiveApply B psi)))
        atTop (nhds 0)) := by sorry

end QAlgorithms.Papers.Independent.Frontier18.P14

end
