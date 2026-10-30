-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P10_constantDepth_sectorInitialization
-- name    : QAlgorithms.Papers.Independent.Extend50.P10.constantDepth_sectorInitialization
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T19:44:16.262927+00:00
-- url     : https://prove2.me/theorems/dd3862b7-1581-47e9-9f87-588d712df6fc
-- title:
--   Constant-depth initialization in every physical sector
-- statement:
--   Fix a local dimension $d\ge2$. For any partition $\lambda\vdash n$ of height at most $d$, place on each column of height $h$ the normalized antisymmetric state
--
--   $$
--   |A_h\rangle=\frac1{\sqrt{h!}}\sum_{\pi\in S_h}\operatorname{sgn}(\pi)|\pi(0),\ldots,\pi(h-1)\rangle,
--   $$
--
--   and tensor these states on disjoint sets of sites, using the fixed cell numbering. Write the resulting column product as $|\Psi_\lambda\rangle$. There exists $D(d)\in\mathbb N$, independent of $n$ and $\lambda$, such that for every $n\ge1$ and every such $\lambda$, a circuit $C$ of arbitrary continuous one- and two-qudit unitary gates on unrestricted wire pairs satisfies
--
--   $$
--   \operatorname{depth}(C)\le D(d),\qquad C|0\rangle^{\otimes n}=|\Psi_\lambda\rangle,\qquad
--   \|\Psi_\lambda\|=1,\qquad P_\lambda|\Psi_\lambda\rangle=|\Psi_\lambda\rangle.
--   $$
--
--   Here each depth layer contains gates with disjoint supports and $P_\lambda$ is the full physical isotypic projector. This prepares a specified state within each sector; it makes no assertion about preparing arbitrary states of that sector or about depth uniform in varying $d$.
-- source:
--   Speeding up Learning Quantum States through Group Equivariant Convolutional Quantum Ansätze, arXiv:2112.07611v3, PDF p. 2, Unnumbered main result: constant-depth preparation in arbitrary physical sectors

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P10

noncomputable section

open scoped Matrix

open QAlgorithms

open QAlgorithms.Schur

open QAlgorithms.Papers.Independent.Information100.P44 (matrixUnit)

namespace QAlgorithms.Papers.Independent.Extend50.P10

attribute [local instance] Classical.propDecidable

/-- PDF pp.2,9–10: for fixed d, a constant number of layers suffices to prepare
some state in every physical sector. D is before n and lambda. The constructed
state is the normalized product of column antisymmetric states; no arbitrary
state-preparation or bound uniform in varying d is asserted. -/
theorem constantDepth_sectorInitialization (d : ℕ) (hd : 2 ≤ d) :
    ∃ D : ℕ, ∀ n : ℕ, 1 ≤ n → ∀ lambda : Partition d n,
      ∃ C : PreparationCircuit d n,
        C.layers.length ≤ D ∧
        act (preparationMatrix C) (ket (fun _ : Fin n => (⟨0, by omega⟩ : Fin d))) =
          columnInitialization lambda ∧
        ‖columnInitialization lambda‖ = 1 ∧
        act (isotypicProjector lambda) (columnInitialization lambda) =
          columnInitialization lambda := by sorry

end QAlgorithms.Papers.Independent.Extend50.P10

end
