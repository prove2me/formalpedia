-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P40_rree_local_channel
-- name    : QAlgorithms.Papers.Independent.Bridge50.P40.rree_local_channel
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T18:56:09.962899+00:00
-- url     : https://prove2.me/theorems/72ea5d17-f0a2-4c21-91a6-2aa964915df9
-- title:
--   Local-channel monotonicity of Petz RREE
-- statement:
--   All registers are finite and nonempty. Density operators have trace one, pure states are normalized, all entropies and logarithms are in base two, and $F(\rho,\sigma)=\|\sqrt\rho\sqrt\sigma\|_1$ denotes root fidelity. Write $S_a$ for Petz Rényi entropy, with support projection at order zero and the von Neumann limit at order one; $S_\infty(\rho)=-\log_2\lambda_{\max}(\rho)$.
--
--   For a bipartite density operator $\rho^{AB}$, let $E_{\rm RE}^{(a)}(A:B)_\rho=\inf_{\sigma\in\mathrm{Sep}(A:B)}D_a(\rho\|\sigma)$, with support-aware Petz divergence and the Umegaki limit at order one. For $0\le a\le2$, every CPTP map $\mathcal E:B\to C$ and every CPTP map $\mathcal G:A\to D$ satisfy
--
--   $$
--   E_{\rm RE}^{(a)}(A:C)_{(\mathrm{id}_A\otimes\mathcal E)(\rho)}\le E_{\rm RE}^{(a)}(A:B)_\rho,\qquad
--   E_{\rm RE}^{(a)}(D:B)_{(\mathcal G\otimes\mathrm{id}_B)(\rho)}\le E_{\rm RE}^{(a)}(A:B)_\rho.
--   $$
--
--   This includes the symmetric local-$A$ assertion stated immediately after (9). The real infimum uses finite upper bounds on extended divergence; a full-rank separable comparison ensures nonemptiness and finiteness on these inputs.
-- source:
--   A strong converse for the quantum state merging protocol, arXiv:1404.5940v1, PDF p. 4, Lemma 1, equation (9)

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P40

noncomputable section

namespace QAlgorithms.Papers.Independent.Bridge50.P40

open scoped Matrix ComplexConjugate

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower)

open QAlgorithms.Papers.Independent.Information100.P22 (bell)

open QAlgorithms.Papers.Independent.Gap20.P11 (IsLOCC productApply marginalAR)

open QAlgorithms.Papers.Independent.Dependency50.P05 (renyiEntropy)

open QAlgorithms.Papers.Independent.Dependency50.P35 (cq)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.4, Lemma 1, (9), and its local-A symmetry note: local CPTP
monotonicity for all orders in [0,2], including the support and Umegaki endpoints. -/
theorem rree_local_channel {A B C D : Type}
    [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    [Nonempty A] [Nonempty B] [Nonempty C] [Nonempty D]
    (rho : Matrix (A × B) (A × B) ℂ) (hrho : IsDensityMatrix rho)
    (a : ℝ) (ha : 0 ≤ a) (ha2 : a ≤ 2)
    (E : Superop B C) (hE : IsChannel E)
    (G : Superop A D) (hG : IsChannel G) :
    rree a (idTensorSuperop E rho) ≤ rree a rho ∧
    rree a (productApply G (fun X : Matrix B B ℂ => X) rho) ≤ rree a rho := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P40

end
