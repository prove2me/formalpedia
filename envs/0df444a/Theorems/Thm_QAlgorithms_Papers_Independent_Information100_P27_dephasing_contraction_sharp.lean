-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P27_dephasing_contraction_sharp
-- name    : QAlgorithms.Papers.Independent.Information100.P27.dephasing_contraction_sharp
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T10:19:34.277649+00:00
-- url     : https://prove2.me/theorems/4b7a151b-f13b-419b-88ef-cb29c5571786
-- title:
--   §9.3: sharpness of the squared contraction factor
-- statement:
--   Fix $0<p<1$ and $0<\gamma<1$. For $z\in\mathbb C$ with $0<|z|<\sqrt{p(1-p)}$, set $\theta_z=\begin{pmatrix}p&z\\overline z&1-p\end{pmatrix}$. These are density matrices with strictly positive coherence $C_r(\theta_z)=H(\Delta\theta_z)-H(\theta_z)$. Under qubit dephasing $Z_\gamma$,
--
--   $$
--   \lim_{\substack{z\to0\0<|z|<\sqrt{p(1-p)}}}\frac{C_r(Z_\gamma(\theta_z))}{C_r(\theta_z)}=\gamma^2.
--   $$
--
--   Consequently any real constant $c$ satisfying $C_r(Z_\gamma(\theta))\le cC_r(\theta)$ for every qubit density matrix must obey $c\ge\gamma^2$. Thus the contraction factor is optimal even without an auxiliary system.
-- source:
--   Static classical-quantum- entanglement trade-offs: an entropic converse and single-letter characterizations, arXiv:2609.23298v1, PDF p. 46, §9.3: sharpness of the squared contraction factor

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P27

noncomputable section

open scoped ComplexConjugate ComplexOrder

attribute [local instance] Classical.decEq Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Information100.P27

/-- arXiv:2609.23298v1 PDF pp.45-46, (9.26)-(9.30): sharpness on the punctured
complex disk of density matrices, with p and gamma in the section's strict interior. -/
theorem dephasing_contraction_sharp (p gamma : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (hgamma0 : 0 < gamma) (hgamma1 : gamma < 1) :
    (∀ z : ℂ, 0 < ‖z‖ → ‖z‖ < Real.sqrt (p * (1-p)) →
      IsDensityMatrix (perturbation p z) ∧ 0 < coherence (perturbation p z)) ∧
    Filter.Tendsto
      (fun z : ℂ => coherence (qubitDephasing gamma (perturbation p z)) /
        coherence (perturbation p z))
      (nhdsWithin 0 {z : ℂ | 0 < ‖z‖ ∧ ‖z‖ < Real.sqrt (p * (1-p))})
      (nhds (gamma ^ 2)) ∧
    (∀ c : ℝ, (∀ theta : Matrix (Fin 2) (Fin 2) ℂ, IsDensityMatrix theta →
      coherence (qubitDephasing gamma theta) ≤ c * coherence theta) → gamma ^ 2 ≤ c) := by sorry

end QAlgorithms.Papers.Independent.Information100.P27

end
