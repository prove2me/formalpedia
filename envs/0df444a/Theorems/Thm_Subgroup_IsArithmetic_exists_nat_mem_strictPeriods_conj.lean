-- Prove2me | Theorems.Thm_Subgroup_IsArithmetic_exists_nat_mem_strictPeriods_conj
-- name    : Subgroup.IsArithmetic.exists_nat_mem_strictPeriods_conj
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.134728+00:00
-- url     : https://prove2.me/theorems/fabaf53f-b200-50fb-9e51-df1019449bf7
-- title:
--   A uniform integer period for all SL₂(ℤ)-conjugates
-- statement:
--   Let $\mathcal{G}$ be a subgroup of $\mathrm{GL}_2(\mathbb{R})$ which is arithmetic in the sense of Mathlib's class `Subgroup.IsArithmetic`; the feature of that hypothesis used here is that the preimage of $\mathcal{G}$ in $\mathrm{SL}_2(\mathbb{Z})$ under the map $\mathrm{SL}_2(\mathbb{Z}) \to \mathrm{GL}_2(\mathbb{R})$ (`Matrix.SpecialLinearGroup.mapGL`) has finite index. The assertion is that there exists a natural number $M$ with $M > 0$ such that for every $\gamma \in \mathrm{SL}_2(\mathbb{Z})$ the real number $M$ belongs to the group of strict periods of the conjugate subgroup $\mathrm{toConjAct}(\mathrm{mapGL}_{\mathbb{R}}\,\gamma) \cdot \mathcal{G}$, that is, of $\gamma\mathcal{G}\gamma^{-1}$ inside $\mathrm{GL}_2(\mathbb{R})$, where $\gamma$ acts through its image in $\mathrm{GL}_2(\mathbb{R})$. Since `Subgroup.strictPeriods` consists of those $x \in \mathbb{R}$ for which the upper unitriangular matrix $\begin{pmatrix} 1 & x \\ 0 & 1\end{pmatrix}$ lies in the subgroup, the conclusion says that one single positive integer $M$ has $T^M = \begin{pmatrix} 1 & M \\ 0 & 1\end{pmatrix} \in \gamma\mathcal{G}\gamma^{-1}$ simultaneously for all $\gamma \in \mathrm{SL}_2(\mathbb{Z})$.
--
--   This is the statement that an arithmetic subgroup of $\mathrm{GL}_2(\mathbb{R})$ admits one integer width that is a period at every cusp, uniformly over all $\mathrm{SL}_2(\mathbb{Z})$-translates, so that the $q$-expansions of all translates $f\mid_k\gamma$ of a modular form can be taken in the same variable $q^{1/M}$. It is used in the construction of equivariant primitives on modular curves and in the proofs of finite-dimensionality and of a Sturm bound for spaces of modular forms on arithmetic groups.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Subgroup_IsArithmetic_exists_nat_mem_strictPeriods_conj.lean

import Mathlib.NumberTheory.ModularForms.Cusps

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped MatrixGroups Pointwise

theorem Subgroup.IsArithmetic.exists_nat_mem_strictPeriods_conj (𝒢 : Subgroup (GL (Fin 2) ℝ)) [𝒢.IsArithmetic] : ∃ M : ℕ, 0 < M ∧ ∀ γ : SL(2, ℤ), (M : ℝ) ∈ (ConjAct.toConjAct (Matrix.SpecialLinearGroup.mapGL ℝ γ) • 𝒢).strictPeriods := by sorry
