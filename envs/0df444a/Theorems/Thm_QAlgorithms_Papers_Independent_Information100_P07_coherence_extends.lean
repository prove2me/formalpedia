-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P07_coherence_extends
-- name    : QAlgorithms.Papers.Independent.Information100.P07.coherence_extends
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T09:35:12.555984+00:00
-- url     : https://prove2.me/theorems/ec4d9d58-48ab-4b60-a719-1df36617f2b8
-- title:
--   Lemma S2: coherence extends protection with unchanged Kraus weights
-- statement:
--   Let a CPTP channel with a fixed finite Kraus family $(K_i)$ fix a positive operator $\omega$. Suppose on a subspace $L$, the same operators act as $\sqrt{p_i}$ times unitaries of $L$, with $p_i\ge0$ and $\sum_i p_i=1$. Construct
--   $$E=\operatorname{span}\{\omega^k x:k\ge0,\ x\in L\}.$$
--   Then each $K_i$ acts on $E$ as $\sqrt{p_i}$ times a unitary of $E$, using the same weights. Zero-weight restrictions vanish. Moreover, $\Omega(P_E)=P_E$ and $P_E\omega=\omega P_E$.
--
--   No separability, product structure, normalization of $\omega$, or containment $L\subseteq\operatorname{supp}\omega$ is assumed. This describes the protection forced by coherence.
-- source:
--   Complete Classification of Reversible Entanglement Transformations of Two Qutrits, arXiv:2610.05234v1, PDF p. 10, Lemma S2: coherence extends protection with unchanged Kraus weights

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P07

noncomputable section

namespace QAlgorithms.Papers.Independent.Information100.P07

open scoped Matrix ComplexConjugate ComplexOrder

open QAlgorithms QAlgorithms.Entanglement

attribute [local instance] Classical.propDecidable Classical.decEq

/-- arXiv:2610.05234v1, PDF p.10, Lemma S2, including its final projector and commutation facts. -/
theorem coherence_extends {m : ℕ} (K : Fin m → Joint) (p : Fin m → ℝ)
    (omega : Joint) (L : Submodule ℂ Space) (hK : IsKrausFamily K)
    (homega : omega.PosSemidef) (hfix : krausApply K omega = omega)
    (hprotect : Protects K L p) :
    Protects K (coherenceSpace omega L) p ∧
    krausApply K (projection (coherenceSpace omega L)) = projection (coherenceSpace omega L) ∧
    projection (coherenceSpace omega L) * omega = omega * projection (coherenceSpace omega L) := by sorry

end QAlgorithms.Papers.Independent.Information100.P07

end
