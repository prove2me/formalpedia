-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier30_P17_fixedInput_conclusiveTeleportation
-- name    : QAlgorithms.Papers.Independent.Frontier30.P17.fixedInput_conclusiveTeleportation
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T15:54:18.277077+00:00
-- url     : https://prove2.me/theorems/58acd90a-f0ed-474e-b7d2-73e20c515b93
-- title:
--   Fixed-input conclusive teleportation: dimension-independent success
-- statement:
--   Let $V=(\mathbb C^d)^{\otimes m}$ in its fixed computational basis, let $\mu$ be probability Haar measure on $U(d)$, and write $|\Phi\rangle=d^{-m/2}\sum_x|x\rangle|x\rangle$. For $C>0$ define the resolved successful operator density and integrated effect by
--   $$
--   E_C(U)=C(I\otimes\overline U^{\otimes m})|\Phi\rangle\langle\Phi|(I\otimes U^{\mathsf T\otimes m}),\qquad M_C=\int E_C(U)\,d\mu(U).
--   $$
--   For an $m$-to-$n$ qudit CPTP channel $\mathcal N$, use its normalized reference-first Choi state $J_{\mathcal N}=(\mathrm{id}\otimes\mathcal N)(|\Phi\rangle\langle\Phi|)$. Assume $\mathcal N$ is unitary equivariant: $\mathcal N(U^{\otimes m}\rho U^{\dagger\otimes m})=U^{\otimes n}\mathcal N(\rho)U^{\dagger\otimes n}$ for every unitary $U$ and every density matrix $\rho$. For a resolved successful outcome $U$, let $K_C(U)$ be Bob's unnormalized output density after measuring $E_C(U)$ on $\rho\otimes J_{\mathcal N}$, tracing out the two measured registers, and applying the correction $U^{\dagger\otimes n}$. Thus this protocol uses one Choi resource and retains $U$ until after correction.
--
--   For every fixed positive integer $m$, there exist $c_m\in(0,1]$ and an integer $D_m\ge1$, chosen before $d,n,\mathcal N,\rho$, such that for every $d\ge D_m$, setting $C=c_m d^{2m}$ gives an integrable positive operator density and a valid successful effect. In operator norm,
--   $$
--   \|M_1\|_{\mathrm{op}}\le\frac{1}{c_m d^{2m}},\qquad 0\preceq M_C\preceq I,\qquad\|M_C\|_{\mathrm{op}}\le1.
--   $$
--   For every output count $n\ge0$, every unitary-equivariant CPTP channel and every normalized input state,
--   $$
--   \operatorname{Pr}(\mathrm{success})=\operatorname{Tr}\!\left[M_C\left(\rho\otimes\frac I{d^m}\right)\right]=c_m,\qquad K_C(U)=c_m\mathcal N(\rho)\quad\text{for every }U.
--   $$
--   The corrected output density is integrable and integrates to $c_m\mathcal N(\rho)$; hence the conditional successful output is exactly $\mathcal N(\rho)$.
--
--   The success constant can depend on $m$ and is independent of dimension, channel, output count and input state. The normalization is a sufficiently small positive multiple of $d^{2m}$. No claim is made about efficient exact discretization or about a constant uniform in $m$.
--
--   **Formalization Note** The positive-$m$ domain follows the positive-input protocol of Section 5.1.1; the separate empty-transform boundary in the mixed Schur capstone is deferred with that capstone.
-- source:
--   The mixed Schur transform: efficient quantum circuit and applications, arXiv:2310.01613v1, PDF p. 29, Section 5.1.1: fixed-m dimension-independent success

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P17

noncomputable section

open MeasureTheory Filter

open scoped Matrix ComplexConjugate ComplexOrder Topology Matrix.Norms.Elementwise

open QAlgorithms.Papers.Independent.Information100.P75 (Register)

open QAlgorithms.Papers.Independent.Information100.P56 (normalizedChoi)

namespace QAlgorithms.Papers.Independent.Frontier30.P17

/-- Section 5.1.1, Eqs.(86)–(90),(93), arXiv:2310.01613v1, PDF pp.29–30:
for each fixed positive input count m there is a positive success probability
c_m independent of dimension, output count, channel and state, for all large d.
The choice C=c_m*d^(2m) is a sufficiently small multiple, not an arbitrary
Omega lower bound on C. No discretization or circuit complexity is asserted. -/
theorem fixedInput_conclusiveTeleportation :
    ∀ m : ℕ, 0 < m → ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧
      ∃ D : ℕ, 1 ≤ D ∧ ∀ d : ℕ, D ≤ d →
        specNorm (conclusiveEffect d m 1) ≤ c⁻¹ / (d : ℝ) ^ (2 * m) ∧
        (∀ a b, Integrable (fun U =>
          conclusiveDensity d m (c * (d : ℝ) ^ (2 * m)) U a b)
          (Schur.unitaryHaar d)) ∧
        (∀ U, (conclusiveDensity d m (c * (d : ℝ) ^ (2 * m)) U).PosSemidef) ∧
        IsEffect (conclusiveEffect d m (c * (d : ℝ) ^ (2 * m))) ∧
        specNorm (conclusiveEffect d m (c * (d : ℝ) ^ (2 * m))) ≤ 1 ∧
        ∀ (n : ℕ) (N : Superop (Register (fun _ : Fin m => d)) (Register (fun _ : Fin n => d))),
          IsChannel N → IsUnitaryEquivariant N →
          ∀ rho : Matrix (Register (fun _ : Fin m => d)) (Register (fun _ : Fin m => d)) ℂ, IsDensityMatrix rho →
            conclusiveProbability (c * (d : ℝ) ^ (2 * m)) rho = c ∧
            (∀ U, correctedOutcome (c * (d : ℝ) ^ (2 * m)) N rho U =
              (c : ℂ) • N rho) ∧
            (∀ a b, Integrable (fun U =>
              correctedOutcome (c * (d : ℝ) ^ (2 * m)) N rho U a b)
              (Schur.unitaryHaar d)) ∧
            (∫ U, correctedOutcome (c * (d : ℝ) ^ (2 * m)) N rho U
              ∂Schur.unitaryHaar d) = (c : ℂ) • N rho := by sorry

end QAlgorithms.Papers.Independent.Frontier30.P17

end
