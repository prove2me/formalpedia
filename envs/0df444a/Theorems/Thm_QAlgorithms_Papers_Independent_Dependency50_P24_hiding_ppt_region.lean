-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P24_hiding_ppt_region
-- name    : QAlgorithms.Papers.Independent.Dependency50.P24.hiding_ppt_region
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T16:18:21.026842+00:00
-- url     : https://prove2.me/theorems/e00d0de7-27df-4690-bf9e-ec96affd59b8
-- title:
--   Lemma 5: PPT region of hiding family
-- statement:
--   All spaces are finite dimensional and have positive dimension. A state means a positive semidefinite operator of trace one. The distinguished product basis $B$ is fixed and is used for both twisting and key measurement. Norms are full trace norms, fidelity $F$ is root fidelity, and logarithms are in bits.
--
--   For $d\ge2$ and $k\ge1$, let $\rho_s=(I+V)/(d^2+d)$ and $\rho_a=(I-V)/(d^2-d)$ be Werner states, $\tau_1=((\rho_s+\rho_a)/2)^{\otimes k}$ and $\tau_2=\rho_s^{\otimes k}$. For $0<p\le1/2$, form Eq.(136) with corner blocks $p(\tau_1-\tau_2)/2$, extreme diagonal blocks $p(\tau_1+\tau_2)/2$, and middle diagonal blocks $(1/2-p)\tau_2$. This is a state and
--
--   $$\rho(p,d,k)\text{ is PPT across }AA':BB'\iff p\le\tfrac13\ \text{ and }\ (d/(d-1))^k\le(1-p)/p.$$
--
--   For every fixed $0<p\le1/3$ and $k\ge1$, some $d\ge2$ makes this state PPT. This identifies the positive-transpose part of the hiding family.
-- source:
--   General paradigm for distilling classical key from quantum states, arXiv:quant-ph/0506189v2, PDF p. 24, Lemma 5: PPT region of hiding family

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P24

noncomputable section

namespace QAlgorithms.Papers.Independent.Dependency50.P24

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

open Finset

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

-- Accepted declarations are imported rather than redeclared locally.

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Information100.P04 (bellProjector)

open QAlgorithms.Papers.Independent.Information100.P07 (positivePart negativePart)

open QAlgorithms.Papers.Independent.Information100.P34 (supportProjector)

open QAlgorithms.Papers.Independent.Information100.P54 (relativeEntropyBits relativeEntanglement)

/-- PDF p.24, Lemma 5; pp.32–33: k>=1 and d>=2. Eq.(136)'s lower-left
plus is corrected to a difference using the preceding mixture and Eq.(200). -/
theorem hiding_ppt_region :
    (∀ d k : ℕ, 2 ≤ d → 1 ≤ k → ∀ p : ℝ, 0 < p → p ≤ 1/2 →
      IsDensityMatrix (hidingFamily p d k) ∧
      ((transposeBob (hidingFamily p d k)).PosSemidef ↔
        p ≤ 1/3 ∧ ((d:ℝ)/(d-1))^k ≤ (1-p)/p)) ∧
    (∀ p : ℝ, 0 < p → p ≤ 1/3 → ∀ k : ℕ, 1 ≤ k →
      ∃ d : ℕ, 2 ≤ d ∧ (transposeBob (hidingFamily p d k)).PosSemidef) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P24

end
