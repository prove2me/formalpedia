-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P26_classical_freeEnergy_and_shannon_limit
-- name    : QAlgorithms.Papers.Independent.Advance50.P26.classical_freeEnergy_and_shannon_limit
-- status  : Proved
-- author  : @Gohan
-- created : 2026-10-29T10:41:39.162454+00:00
-- url     : https://prove2.me/theorems/6bb3b956-f570-47d0-a25a-11fee6d1ddde
-- title:
--   Normalized classical free energy and the two Shannon limits
-- statement:
--   Let $I$ be a nonempty finite set and let $p=(p_i)_{i\in I}$ satisfy $p_i>0$ and $\sum_i p_i=1$. Work in units where Boltzmann's constant is one, fix $T_0>0$, and construct the energies $E_i=-T_0\ln p_i$. For positive $T$, set $Z_E(T)=\sum_i\exp(-E_i/T)$ and $F_E(T)=-T\ln Z_E(T)$. Write $S_q(p)=\ln(\sum_i p_i^q)/(1-q)$ for $q>0$, $q\ne1$, and $S_1(p)=-\sum_i p_i\ln p_i$. Then for every positive $T\ne T_0$,
--   $$
--   F_E(T)=-(T-T_0)S_{T_0/T}(p).
--   $$
--   Moreover, both expressions in the quotient identity converge to Shannon entropy:
--   $$
--   \lim_{\substack{T\to T_0\\ T>0,\ T\ne T_0}}S_{T_0/T}(p)
--   =\lim_{\substack{T\to T_0\\ T>0,\ T\ne T_0}}\frac{-F_E(T)}{T-T_0}
--   =S_1(p).
--   $$
--   The construction gives $Z_E(T_0)=1$ and hence $F_E(T_0)=0$. The limits describe the nontrivial order-one extension of the entropy identity.
-- source:
--   Renyi Entropy and Free Energy, arXiv:1102.2098v4, PDF p. 2, Section 1, Eq. (2) and its following quotient-limit sentence

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P26

noncomputable section

open Filter

open scoped BigOperators Topology Matrix.Norms.L2Operator

namespace QAlgorithms.Papers.Independent.Advance50.P26

open QAlgorithms.Papers.Independent.Support50.P15 (shannonEntropyNats)

open QAlgorithms.ZeroSum (classicalGibbs)

open QAlgorithms.Papers.Independent.Dependency50.P35 (spectralPower)

/-- PDF pp.1-2, Section 1, (2) and the sentence immediately after its calculation:
construct E_i = -T0 log p_i from a strictly positive normalized finite law. The
identity holds at each positive T != T0, and both sides of the quotient identity
S_(T0/T)(p) = -F_E(T)/(T-T0) tend to Shannon entropy. The limits concern the quotient
identity in the proof, not the two sides of (2), which both tend to zero. -/
theorem classical_freeEnergy_and_shannon_limit {I : Type*} [Fintype I] [Nonempty I]
    (p : I → ℝ) (hp : ∀ i, 0 < p i) (hnorm : ∑ i, p i = 1)
    (T0 : ℝ) (hT0 : 0 < T0) :
    (∀ T : ℝ, 0 < T → T ≠ T0 →
      classicalFreeEnergy (referenceEnergies p T0) T =
        -(T - T0) * classicalRenyiNats p (T0 / T)) ∧
    Tendsto (fun T : ℝ => classicalRenyiNats p (T0 / T))
      (nhdsWithin T0 {T : ℝ | 0 < T ∧ T ≠ T0}) (𝓝 (shannonEntropyNats (fun i => p ((Fintype.equivFin I).symm i)))) ∧
    Tendsto (fun T : ℝ => -classicalFreeEnergy (referenceEnergies p T0) T / (T - T0))
      (nhdsWithin T0 {T : ℝ | 0 < T ∧ T ≠ T0}) (𝓝 (shannonEntropyNats (fun i => p ((Fintype.equivFin I).symm i)))) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P26

end
