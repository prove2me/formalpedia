-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P50_proposition_4_3
-- name    : QAlgorithms.Papers.Independent.Information100.P50.proposition_4_3
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T12:00:17.795986+00:00
-- url     : https://prove2.me/theorems/edd81bf2-ff62-4f15-ba31-ab00967b504b
-- title:
--   Proposition 4.3: For effects E,Eprime, specNorm((E-E^2)-(Eprime-Eprime^2))≤specNorm(E-Eprime), and specNorm(g_hash(E)-g_hash(Ep
-- statement:
--   All spaces are finite-dimensional complex Euclidean spaces. Input and output dimensions are positive wherever states or extreme eigenvalues occur. The Choi matrix $J$ is unnormalized and has output factor first. Write $\|\Theta\|_\diamond$ for the full completely bounded trace norm, $\|A\|_\infty$ for the operator norm, and $\Theta^*$ for the Hilbert–Schmidt adjoint.
--
--   For a fixed linearly independent Kraus family $(V_k)_{k=1}^r$, put $\Omega(X)=\sum_k V_kXV_k^*$, $W=[\operatorname{vec}(V_1)\ \cdots\ \operatorname{vec}(V_r)]$, and $\Psi_T(X)=\sum_{k,l}T_{kl}V_kXV_l^*$. An effect $T$ determines the pair $(\Psi_T,\Psi_{I-T})$ with common sum $\Omega$. This parametrizes exactly the source's pairs and derivatives, by the ARN correspondence. All derivatives compared use this same family.
--
--   For any two effects $E,E'$ on the same finite space, with $g_\#(t)=\sqrt{t(1-t)}$,
--
--   $$\|(E-E^2)-(E'-E'^2)\|_\infty\le\|E-E'\|_\infty,\qquad \|g_\#(E)-g_\#(E')\|_\infty\le\sqrt{\|E-E'\|_\infty}.$$
--
--   Consequently, for the two pairs defined by effects $T_1,T_2$ in a common ARN frame,
--
--   $$\|\Psi_{T_1}\#\Psi_{I-T_1}-\Psi_{T_2}\#\Psi_{I-T_2}\|_\diamond\le\|\Omega\|_\diamond\sqrt{\|T_1-T_2\|_\infty}.$$
--
--   No mutual commutativity is assumed. The estimate transfers the operator modulus to CP-map means.
-- source:
--   Quantitative upper bounds for certain quantum channel divergences, arXiv:2610.16270v1, PDF p. 13, Proposition 4.3

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P50

noncomputable section

open scoped Matrix ComplexConjugate ENNReal Topology ComplexOrder Kronecker

open Filter Set

namespace QAlgorithms.Papers.Independent.Information100.P50

/-- Proposition 4.3, source PDF pp.13–14. The effects need not commute with each other;
the last clause is the common-sum CP-map consequence. -/
theorem proposition_4_3 :
    (∀ (n : ℕ) (E F : M n), IsEffect E → IsEffect F →
      specNorm ((E - E ^ 2) - (F - F ^ 2)) ≤ specNorm (E - F) ∧
      specNorm (cfc gHash E - cfc gHash F) ≤ Real.sqrt (specNorm (E - F))) ∧
    (∀ (dx dy r : ℕ),
      ∀ (V : Fin r → Matrix (Fin dy) (Fin dx) ℂ), LinearIndependent ℂ V →
      ∀ (T1 T2 : M r), IsEffect T1 → IsEffect T2 →
      cbTraceNorm (cpGeometricMean (arnFamily V T1) (arnFamily V (1 - T1)) -
        cpGeometricMean (arnFamily V T2) (arnFamily V (1 - T2))) ≤
      cbTraceNorm (krausMap V) * Real.sqrt (specNorm (T1 - T2))) := by sorry

end QAlgorithms.Papers.Independent.Information100.P50

end
