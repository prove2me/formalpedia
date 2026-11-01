-- Prove2me | Theorems.Thm_ShorAdditivityEquiv_holevoCapacity_superadditive
-- name    : ShorAdditivityEquiv.holevoCapacity_superadditive
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T15:31:23.423587+00:00
-- url     : https://prove2.me/theorems/da04db3a-a4dd-478e-bbc4-b998c86990be
-- title:
--   §2, p. 3 — the easy direction $\chi_{N_1\otimes N_2}\ge\chi_{N_1}+\chi_{N_2}$
-- statement:
--   Let $N_1$, $N_2$ be quantum channels with nonempty finite-dimensional input and output spaces. Then
--   $$
--   \chi_{N_1\otimes N_2} \ge \chi_{N_1}+\chi_{N_2},
--   $$
--   where $\chi$ is the Holevo capacity of Eq. (1). The paper notes that "the $\ge$ relation is easy; the open question is the $\le$ relation". It is used whenever an additivity hypothesis is invoked in one direction only.
--
--   Differences from the source:
--   - encoding: max / min over ensembles {p_i, |v_i⟩} or over vectors |φ⟩ (Eqs. (1)–(3), Theorem 1 (i)) → sSup / sInf over all finite pure-state ensembles of every size, or over all unit vectors; reason: on the domain of the statement (channels, density matrices, nonempty spaces) every set is nonempty and bounded (0 ≤ · ≤ log₂ d_out) and the extremum is attained (Carathéodory, compact unit sphere), so the values coincide
--   - encoding: spaces C^{d×d}, H_in, H_{A1}, … of finite dimension → nonempty finite types (Fintype, DecidableEq, Nonempty) in Type; reason: a 0-dimensional space carries no state, so Nonempty excludes no instance of the paper
--   - encoding: quantum channel (CPT map) → QAlgorithms.IsChannel (a finite Kraus family with Σ A_k†A_k = I); reason: the paper gives this operator-sum form as an equivalent characterization of finite-dimensional CPT maps (pp.2–3)
--   - encoding: vectors |φ⟩, |v_i⟩ of the input space → unit vectors (‖φ‖ = 1); reason: |φ⟩⟨φ| is meant as a state (p.4: "the minimization ranges over states |φ⟩"); ensemble members are states
--   - encoding: N1 ⊗ N2 → ShorEBAdditivity.tensorChannel N₁ N₂, defined on every operator by the matrix-unit expansion; reason: for linear maps it is the unique linear map with (N₁ ⊗ N₂)(X ⊗ Y) = N₁(X) ⊗ N₂(Y); it acts on entangled inputs too
-- source:
--   Shor, Equivalence of Additivity Questions in Quantum Information Theory, arXiv:quant-ph/0305035v4, §2, p. 3

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_ShorEBAdditivity_tensorChannel
import Definitions.Def_ShorAdditivityEquiv_holevoCapacity

open QAlgorithms

namespace ShorAdditivityEquiv

/-- Shor, *Equivalence of Additivity Questions in Quantum Information Theory*, arXiv:quant-ph/0305035v4, §2, p.3, unnumbered: "The question of whether the quantum capacity is given by the
single-symbol Holevo capacity χN is the question of whether the capacity χN is additive; that
is, whether χN1⊗N2 = χN1 + χN2. The ≥ relation is easy; the open question is the ≤ relation."

The easy relation `χ_{N1⊗N2} ≥ χ_{N1} + χ_{N2}` for every pair of channels.

**Formalization Note.** `χ` is `holevoCapacity` (Eq. (1), pure-state ensembles). The channels
act on nonempty finite types in `Type` (`QAlgorithms.IsChannel` for "CPT map"), and `N₁ ⊗ N₂`
is `ShorEBAdditivity.tensorChannel`. -/
theorem holevoCapacity_superadditive {I₁ O₁ I₂ O₂ : Type} [Fintype I₁] [DecidableEq I₁]
    [Nonempty I₁] [Fintype O₁] [DecidableEq O₁] [Nonempty O₁] [Fintype I₂] [DecidableEq I₂]
    [Nonempty I₂] [Fintype O₂] [DecidableEq O₂] [Nonempty O₂] (N₁ : Superop I₁ O₁)
    (N₂ : Superop I₂ O₂) (hN₁ : IsChannel N₁) (hN₂ : IsChannel N₂) :
    holevoCapacity N₁ + holevoCapacity N₂ ≤
      holevoCapacity (ShorEBAdditivity.tensorChannel N₁ N₂) := by sorry

end ShorAdditivityEquiv
