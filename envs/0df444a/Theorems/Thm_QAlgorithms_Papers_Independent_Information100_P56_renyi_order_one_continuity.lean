-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P56_renyi_order_one_continuity
-- name    : QAlgorithms.Papers.Independent.Information100.P56.renyi_order_one_continuity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T12:19:09.164514+00:00
-- url     : https://prove2.me/theorems/ad9258f0-719e-436b-9020-d757e114e6cf
-- title:
--   Lemma V.2: continuity at Renyi order one
-- statement:
--   Let the input alphabet be finite and nonempty, and let Bob and Eve have nonzero finite-dimensional output spaces. Each channel output is a positive semidefinite matrix of trace one. Entropies and information rates use natural logarithms, with $0\log0=0$. Let $G$ be a finite group. For $R=B,E$, let $U_R$ be a possibly projective unitary representation and $W_R(g)=U_R(g)\rho_RU_R(g)^\dagger$ for a density seed $\rho_R$. Write $\rho_R(P)=\sum_gP(g)W_R(g)$ and $\Delta(P)=H(\rho_B(P))-H(\rho_E(P))$. Fix $P_1,P_3$ and $\omega_v=\rho_E(L_vP_1)$, let $S=\operatorname{supp}P_3$, and put $\sigma_E=\sum_vP_3(v)\omega_v$ and $J_\alpha(Q)=\sum_{v\in S}Q(v)D_\alpha(\omega_v\|\sigma_E)$. Then
--
--   $$\lim_{t\downarrow0}J_{1+t}(P_3)=\sum_{v\in S}P_3(v)D(\omega_v\|\sigma_E)=I(V;E).$$
--
--   For every fixed $t\in(0,1]$, $Q\mapsto J_{1+t}(Q)$ is continuous on the simplex of laws supported on $S$. All divergences are finite on this support. This supplies continuity for the arbitrary-outer-law secrecy bound.
-- source:
--   From Symmetry to Secrecy: Covariant Classical--Quantum Wiretap Channels, arXiv:2610.03580v1, PDF p. 10, Lemma V.2: continuity at Renyi order one

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P56

noncomputable section

namespace QAlgorithms.Papers.Independent.Information100.P56

open scoped ComplexConjugate ComplexOrder Matrix

attribute [local instance] Classical.propDecidable

/-- Lemma V.2, p.10: one-sided continuity at order one, and continuity in the type
on the simplex supported in P3. All divergences in the sum are finite by construction. -/
theorem renyi_order_one_continuity
    {G E : Type*} [Group G] [Fintype G] [Fintype E] [DecidableEq E] [Nonempty E]
    (UE : ProjectiveRep G E) (rhoE : Matrix E E ℂ) (hE : QAlgorithms.IsDensityMatrix rhoE)
    (P1 P3 : G → ℝ) (h1 : IsLaw P1) (h3 : IsLaw P3) :
    let omega := induced (orbit UE rhoE) P1
    Filter.Tendsto (fun t : ℝ => renyiJ (1 + t) P3 P3 omega)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (holevo P3 omega)) ∧
    ((∑ v ∈ Finset.univ.filter (fun v => 0 < P3 v), P3 v *
      ((cfc (fun x : ℝ => x * Real.log x) (omega v) -
        omega v * cfc Real.log (average omega P3)).trace.re)) = holevo P3 omega) ∧
    (∀ t : ℝ, 0 < t → t ≤ 1 →
      ContinuousOn (fun Q : G → ℝ => renyiJ (1 + t) P3 Q omega)
        {Q | IsLaw Q ∧ ∀ v, P3 v = 0 → Q v = 0}) := by sorry

end QAlgorithms.Papers.Independent.Information100.P56

end
