-- Prove2me | Theorems.Thm_WeinbergLeptons_vector_boson_spectrum
-- name    : WeinbergLeptons.vector_boson_spectrum
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-24T19:11:59.330753+00:00
-- url     : https://prove2.me/theorems/35e65a62-3fb8-4c0d-84eb-da5e5ce37ab7
-- title:
--   Weinberg 1967: spin-one mass spectrum and photon identification
-- statement:
--   Let $g,g',\lambda$ be real with $g^2+g'^2>0$, and let $\mathcal M$ be the mass-squared matrix of the spin-one fields $(A^1,A^2,A^3,B)$ read off from eq. (7). Then:
--
--   1. $W_\mu=2^{-1/2}(A_\mu^1+iA_\mu^2)$ has mass $M_W=\tfrac12\lambda g$: $\mathcal Mw=M_W^2w$ (eqs. 8–9);
--   2. $Z_\mu=(g^2+g'^2)^{-1/2}(gA_\mu^3+g'B_\mu)$ has mass $M_Z=\tfrac12\lambda(g^2+g'^2)^{1/2}$: $\mathcal Mz=M_Z^2z$ (eqs. 10, 12);
--   3. $A_\mu=(g^2+g'^2)^{-1/2}(-g'A_\mu^3+gB_\mu)$ is massless: $\mathcal Ma=0$ (eqs. 11, 13);
--   4. $z,a$ are orthonormal;
--   5. for all $T_3,Y$ and all field values,
--   $$gT_3A^3+g'YB=-e\,(T_3-Y)\,A+\frac{g^2T_3+g'^2Y}{(g^2+g'^2)^{1/2}}\,Z,\qquad e=\frac{gg'}{(g^2+g'^2)^{1/2}},$$
--   so the massless field couples to the charge $Q=T_3-Y$ with strength $e$ (eq. 15).
--
--   This is the central tree-level prediction of the model: spontaneous breaking of $SU(2)\times U(1)$ leaves exactly one massless gauge boson, the photon, together with massive $W^\pm$ and $Z$ whose masses and the electric charge are fixed by $g,g',\lambda$.
-- source:
--   S. Weinberg, A Model of Leptons, Phys. Rev. Lett. 19, 1264-1266 (1967), https://doi.org/10.1103/PhysRevLett.19.1264, pp. 1264-1265, eqs. (7)-(15)

import Definitions.Def_WeinbergLeptons_Model

open Matrix

namespace WeinbergLeptons

theorem vector_boson_spectrum (g g' lam : ℝ) (hN : 0 < g ^ 2 + g' ^ 2) :
    (massSqMatrix g g' lam).map (fun x : ℝ => (x : ℂ)) *ᵥ wVec = ((wMass g lam : ℂ) ^ 2) • wVec ∧
    massSqMatrix g g' lam *ᵥ zVec g g' = (zMass g g' lam ^ 2) • zVec g g' ∧
    massSqMatrix g g' lam *ᵥ photonVec g g' = 0 ∧
    zVec g g' ⬝ᵥ zVec g g' = 1 ∧ photonVec g g' ⬝ᵥ photonVec g g' = 1 ∧
    zVec g g' ⬝ᵥ photonVec g g' = 0 ∧
    (∀ T3 Y : ℝ, ∀ V : Fin 4 → ℝ, g * T3 * V 2 + g' * Y * V 3 =
      -electricCharge g g' * (T3 - Y) * (photonVec g g' ⬝ᵥ V) +
        (g ^ 2 * T3 + g' ^ 2 * Y) / Real.sqrt (g ^ 2 + g' ^ 2) * (zVec g g' ⬝ᵥ V)) := by sorry

end WeinbergLeptons
