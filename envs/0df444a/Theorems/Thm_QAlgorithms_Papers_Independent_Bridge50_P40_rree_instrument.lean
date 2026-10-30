-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P40_rree_instrument
-- name    : QAlgorithms.Papers.Independent.Bridge50.P40.rree_instrument
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T18:56:56.50363+00:00
-- url     : https://prove2.me/theorems/ac13362f-5a43-49c5-9e0c-d4ff0b5dd356
-- title:
--   Flagged and average monotonicity of Petz RREE
-- statement:
--   All registers are finite and nonempty. Density operators have trace one, pure states are normalized, all entropies and logarithms are in base two, and $F(\rho,\sigma)=\|\sqrt\rho\sqrt\sigma\|_1$ denotes root fidelity. Write $S_a$ for Petz Rényi entropy, with support projection at order zero and the von Neumann limit at order one; $S_\infty(\rho)=-\log_2\lambda_{\max}(\rho)$.
--
--   Write $E_{\rm RE}^{(a)}(A:B)_\rho=\inf_{\sigma\in\mathrm{Sep}(A:B)}D_a(\rho\|\sigma)$ for the relative entropy of entanglement formed from support-aware Petz divergence.
--
--   Let $\rho^{AB}$ be a density operator and let $\{\mathcal E_x:A\to C\}_{x\in X}$ be a finite CP instrument whose sum is trace preserving. Set $T_x=(\mathcal E_x\otimes\mathrm{id}_B)(\rho)$, $p_x=\operatorname{Tr}T_x$, and $\theta_x=T_x/p_x$ when $p_x>0$; at $p_x=0$ choose any fixed normalized fallback density. Define $\tau^{XCB}=\sum_x|x\rangle\langle x|\otimes T_x$, with the orthogonal flag on Alice's side. For $1<a\le2$,
--
--   $$
--   E_{\rm RE}^{(a)}(A:B)_\rho\ge E_{\rm RE}^{(a)}(XC:B)_\tau\ge\sum_xp_xE_{\rm RE}^{(a)}(C:B)_{\theta_x}.
--   $$
--
--   Both inequalities concern the instrument's computed output, including zero-probability outcomes; no monotonicity assertion is made a hypothesis.
-- source:
--   A strong converse for the quantum state merging protocol, arXiv:1404.5940v1, PDF p. 5, Lemma 3, equation (10)

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

/-- PDF pp.5--6, Lemma 3, (10): both flagged and average monotonicity.
Zero-probability branches use a fixed normalized fallback, not an extra premise. -/
theorem rree_instrument {A B C X : Type}
    [Fintype A] [Fintype B] [Fintype C] [Fintype X]
    [Nonempty A] [Nonempty B] [Nonempty C] [Nonempty X]
    (rho : Matrix (A × B) (A × B) ℂ) (hrho : IsDensityMatrix rho)
    (E : TypedLocalInstrument A C X) (a : ℝ) (ha : 1 < a) (ha2 : a ≤ 2) :
    rree a (E.flagged rho) ≤ rree a rho ∧
    (∑ x, E.weight rho x * rree a (E.normalized rho x)) ≤ rree a (E.flagged rho) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P40

end
