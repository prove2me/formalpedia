-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier30_P17_twoInput_conclusiveTeleportation
-- name    : QAlgorithms.Papers.Independent.Frontier30.P17.twoInput_conclusiveTeleportation
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T15:53:34.211979+00:00
-- url     : https://prove2.me/theorems/a730ab9b-e9ff-40dd-9cb3-410d2522f652
-- title:
--   Two-input conclusive teleportation: exact success and corrected output
-- statement:
--   Let $V=(\mathbb C^d)^{\otimes m}$ in its fixed computational basis, let $\mu$ be probability Haar measure on $U(d)$, and write $|\Phi\rangle=d^{-m/2}\sum_x|x\rangle|x\rangle$. For $C>0$ define the resolved successful operator density and integrated effect by
--   $$
--   E_C(U)=C(I\otimes\overline U^{\otimes m})|\Phi\rangle\langle\Phi|(I\otimes U^{\mathsf T\otimes m}),\qquad M_C=\int E_C(U)\,d\mu(U).
--   $$
--   For an $m$-to-$n$ qudit CPTP channel $\mathcal N$, use its normalized reference-first Choi state $J_{\mathcal N}=(\mathrm{id}\otimes\mathcal N)(|\Phi\rangle\langle\Phi|)$. Assume $\mathcal N$ is unitary equivariant: $\mathcal N(U^{\otimes m}\rho U^{\dagger\otimes m})=U^{\otimes n}\mathcal N(\rho)U^{\dagger\otimes n}$ for every unitary $U$ and every density matrix $\rho$. For a resolved successful outcome $U$, let $K_C(U)$ be Bob's unnormalized output density after measuring $E_C(U)$ on $\rho\otimes J_{\mathcal N}$, tracing out the two measured registers, and applying the correction $U^{\dagger\otimes n}$. Thus this protocol uses one Choi resource and retains $U$ until after correction.
--
--   Take $m=2$ and $d\ge2$, and set $C=d^3(d-1)/2$. Let $S$ swap the two qudits of $V$ and let $I$ denote the identity on $V$. The density $E_C$ is integrable and positive semidefinite, and
--   $$
--   M_C=\frac{C}{d^2(d^2-1)}\left[I\otimes I+S\otimes S-\frac{S\otimes I+I\otimes S}{d}\right],\qquad 0\preceq M_C\preceq I\otimes I,\qquad\|M_C\|_{\mathrm{op}}\le1.
--   $$
--   For every output count $n\ge0$, every such channel and every normalized input state, the success probability and corrected outcome density satisfy
--   $$
--   \operatorname{Tr}\!\left[M_C\left(\rho\otimes\frac I{d^2}\right)\right]=p_d=\frac{d-1}{2d}\ge\frac14,\qquad K_C(U)=p_d\mathcal N(\rho)\quad\text{for every }U.
--   $$
--   The corrected density is integrable and its integral is $p_d\mathcal N(\rho)$, so conditioning on success gives exactly $\mathcal N(\rho)$. Moreover, $\lim_{d\to\infty}p_d=1/2$.
--
--   This computes a dimension-independent conclusive success guarantee while retaining the classical outcome needed for the output correction. It makes no circuit or discretization cost claim.
-- source:
--   The mixed Schur transform: efficient quantum circuit and applications, arXiv:2310.01613v1, PDF p. 29, Section 5.1.1: two-input conclusive teleportation success

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P17

noncomputable section

open MeasureTheory Filter

open scoped Matrix ComplexConjugate ComplexOrder Topology Matrix.Norms.Elementwise

open QAlgorithms.Papers.Independent.Information100.P75 (Register)

open QAlgorithms.Papers.Independent.Information100.P56 (normalizedChoi)

namespace QAlgorithms.Papers.Independent.Frontier30.P17

/-- Section 5.1.1, Eqs.(86)–(92), arXiv:2310.01613v1, PDF p.29:
the two-input protocol is a valid conclusive measurement, has the displayed
SWAP effect, and implements any equivariant CPTP channel on success with
probability (d-1)/(2d), at least 1/4. The resolved outcome is corrected before
forgetting U. The success probability tends to 1/2 as d tends to infinity. -/
theorem twoInput_conclusiveTeleportation :
    (∀ d : ℕ, 2 ≤ d →
      (∀ a b, Integrable (fun U => conclusiveDensity d 2 (twoInputScale d) U a b)
        (Schur.unitaryHaar d)) ∧
      (∀ U, (conclusiveDensity d 2 (twoInputScale d) U).PosSemidef) ∧
      conclusiveEffect d 2 (twoInputScale d) = twoInputEffectFormula d ∧
      IsEffect (conclusiveEffect d 2 (twoInputScale d)) ∧
      specNorm (conclusiveEffect d 2 (twoInputScale d)) ≤ 1 ∧
      (1 / 4 : ℝ) ≤ ((d : ℝ) - 1) / (2 * (d : ℝ)) ∧
      ∀ (n : ℕ) (N : Superop (Register (fun _ : Fin 2 => d)) (Register (fun _ : Fin n => d))),
        IsChannel N → IsUnitaryEquivariant N →
        ∀ rho : Matrix (Register (fun _ : Fin 2 => d)) (Register (fun _ : Fin 2 => d)) ℂ, IsDensityMatrix rho →
          conclusiveProbability (twoInputScale d) rho =
            ((d : ℝ) - 1) / (2 * (d : ℝ)) ∧
          (∀ U, correctedOutcome (twoInputScale d) N rho U =
            ((((d : ℝ) - 1) / (2 * (d : ℝ)) : ℝ) : ℂ) • N rho) ∧
          (∀ a b, Integrable (fun U => correctedOutcome (twoInputScale d) N rho U a b)
            (Schur.unitaryHaar d)) ∧
          (∫ U, correctedOutcome (twoInputScale d) N rho U ∂Schur.unitaryHaar d) =
            ((((d : ℝ) - 1) / (2 * (d : ℝ)) : ℝ) : ℂ) • N rho) ∧
    Tendsto (fun d : ℕ => ((d : ℝ) - 1) / (2 * (d : ℝ))) atTop
      (nhds (1 / 2 : ℝ)) := by sorry

end QAlgorithms.Papers.Independent.Frontier30.P17

end
