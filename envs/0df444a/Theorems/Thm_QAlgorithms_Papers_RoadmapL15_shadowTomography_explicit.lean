-- Prove2me | Theorems.Thm_QAlgorithms_Papers_RoadmapL15_shadowTomography_explicit
-- name    : QAlgorithms.Papers.RoadmapL15.shadowTomography_explicit
-- status  : Open
-- author  : @Goku
-- created : 2026-10-18T19:28:19.978452+00:00
-- url     : https://prove2.me/theorems/ddcc73f6-b788-4457-bc12-dc2314658e7d
-- title:
--   Explicit shadow tomography with a polylogarithmic copy bound
-- statement:
--   There are universal constants $C>0$ and $p\in\mathbb N$ and one explicit adaptive measurement constructor with the following property. Let $D,M\ge1$ be integers, let $E_1,\ldots,E_M$ be known two-outcome measurement effects on $\mathbb C^D$ (so $0\preceq E_i\preceq I$), and let $0<\varepsilon,\delta<1$. The constructor depends on these known data and not on the unknown state.
--
--   Write $L_D=\max\{1,\log D\}$, $L_M=\max\{1,\log M\}$, $L_\delta=\max\{1,\log(1/\delta)\}$, $L_\varepsilon=\max\{1,\log(1/\varepsilon)\}$, $L_{LM}=\max\{1,\log L_M\}$, and $L_{LD}=\max\{1,\log L_D\}$. The constructed procedure uses $k$ independent copies of the unknown state, with
--
--   $$
--   k\le\left\lceil C\varepsilon^{-4}L_\delta L_M^4 L_D(1+L_{LM}+L_{LD}+L_\varepsilon)^p\right\rceil.
--   $$
--
--   For every density matrix $\rho$ on $\mathbb C^D$, a run on $\rho^{\otimes k}$ returns numbers $b_1,\ldots,b_M\in[0,1]$ satisfying
--
--   $$
--   \Pr\!\left[\forall i\in\{1,\ldots,M\},\ |b_i-\operatorname{Tr}(E_i\rho)|\le\varepsilon\right]\ge1-\delta.
--   $$
--
--   Collective measurements, adaptive measurements, temporary ancillas, and unrestricted known-data classical computation are permitted. The procedure composes physical quantum-OR decision programs, the paper's binary gentle search over signed amplified deviation effects, and classical matrix multiplicative weights. This estimates the entire specified list simultaneously without reconstructing the unknown density matrix in trace distance.
--
--   **Formalization Note** The finite adaptive instrument programs carry normalized Kraus families. The constructor supplies actual physical decision programs, not an assumed accuracy contract or a state oracle. The source composition is executed by chunk-local recursive definitions. The logarithm floors extend the asymptotic notation to $D=1$, $M=1$, and other finite boundary regimes; they introduce no additional asymptotic parameter dependence. No computation-time or gate-complexity assertion is made.
-- source:
--   Shadow Tomography of Quantum States, arXiv:1711.01053v2, Theorem 2 (Shadow Tomography Theorem); Problem 1, PDF p. 3. https://arxiv.org/abs/1711.01053v2 . PDF SHA-256: dcb7ad22e3ea2a6a0dd138fdcc4e8bb7d7a11c3e30109d1cf2d229e3ae2e7dea.

import Definitions.Def_QAlgorithms_Defs_ShadowTomographyPrograms
import Definitions.Def_QAlgorithms_Papers_RoadmapL15_Model
set_option autoImplicit false

noncomputable section

open scoped Matrix ComplexOrder

namespace QAlgorithms.Papers.RoadmapL15

open CopyMeasurements ShadowTomography












/-- Aaronson, Shadow Tomography of Quantum States, arXiv:1711.01053v2,
Theorem 2, PDF p.3; Problem 1, p.2; mixed-state/effect conventions, p.12.
The explicit procedure is the physical gentle-search/online-learning composition on p.19.
The p.15 restatement and earlier postselection proof have an epsilon^{-5} bound;
this statement uses the headline epsilon^{-4} bound obtained by the p.19 replacement.
Floored logarithms extend the asymptotic bound to the positive-integer boundary cases. -/
theorem shadowTomography_explicit :
    ∃ C : ℝ, 0 < C ∧ ∃ p : ℕ, ∃ F : SourceCompositionFamily,
      ∀ D M : ℕ, 1 ≤ D → 1 ≤ M →
      ∀ E : Fin M → Matrix (Fin D) (Fin D) ℂ, (∀ i, IsEffect (E i)) →
      ∀ eps delta : ℝ, 0 < eps → eps < 1 → 0 < delta → delta < 1 →
        let S := F.construct D M E eps delta
        S.copies ≤ ⌈C * eps⁻¹ ^ 4 * max 1 (Real.log delta⁻¹) *
          max 1 (Real.log M) ^ 4 * max 1 (Real.log D) *
          (1 + max 1 (Real.log (max 1 (Real.log M))) +
            max 1 (Real.log (max 1 (Real.log D))) + max 1 (Real.log eps⁻¹)) ^ p⌉₊ ∧
        IsAccurate (sourceProcedure S E eps delta) E eps delta := by sorry

end QAlgorithms.Papers.RoadmapL15
