-- Prove2me | Theorems.Thm_SlashInvariantForm_coe_trace_gammaH_eq_add_heckeU_slash_alGL_inv
-- name    : SlashInvariantForm.coe_trace_gammaH_eq_add_heckeU_slash_alGL_inv
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.134728+00:00
-- url     : https://prove2.me/theorems/45fa1725-80a9-5a43-afe9-7ff2e32292be
-- title:
--   Trace to level M/p equals f + Uₚ(f∣ W⁻¹)
-- statement:
--   Fix a natural number $M$ with $M \neq 0$, a prime $p$, and an Atkin–Lehner datum $W$ at $(M,p)$: a factorisation $M = p\,W.R$ together with integers $a,b$ satisfying $pa - W.R\,b = 1$. Let $H \le (\mathbb{Z}/M)^\times$ be a subgroup containing every unit that becomes trivial under the reduction $(\mathbb{Z}/M)^\times \to (\mathbb{Z}/W.R)^\times$ attached to $W.R \mid M$, and let $H'$ be the image of $H$ under that reduction. Write $\Gamma_H(M) \le \mathrm{GL}_2(\mathbb{R})$ for the image of the group of matrices in $\mathrm{SL}_2(\mathbb{Z})$ whose lower-left entry is divisible by $M$ and whose lower-right entry reduces into $H$, and likewise $\Gamma_{H'}(W.R)$; it is assumed, as an instance, that $\Gamma_H(M)$ has finite relative index in $\Gamma_{H'}(W.R)$. Let $k \in \mathbb{Z}$ and let $f$ belong to any type $F$ of functions on the upper half-plane valued in $\mathbb{C}$ that are invariant under the weight-$k$ slash action of $\Gamma_H(M)$. Then, as functions on the upper half-plane, the trace `SlashInvariantForm.trace` of $f$ to $\Gamma_{H'}(W.R)$ equals $$f + \sum_{j=0}^{p-1} \bigl(f \mid_k W^{-1}\bigr) \Bigl|_k \begin{pmatrix} 1 & j \\ 0 & p\end{pmatrix},$$ where $W^{-1}$ is the inverse in $\mathrm{GL}_2(\mathbb{R})$ of the real matrix obtained from the integral Atkin–Lehner matrix of $W$, of determinant $p$, and the sum is the operator [`ModularForm.heckeU`](def/ModularForm_HeckeOperator.html#L93) in weight $k$ at $p$.
--
--   This is the classical formula for the trace from level $M$ to level $M/p$ along the Atkin–Lehner matrix at $p$, identifying the trace defined abstractly as a sum over a coset space with the explicit expression $f + U_p(f \mid_k W^{-1})$. It feeds the analysis of $q$-expansions of traces in [`ModularForm.exists_map_eq_qExpansion_smul_trace_mul_pow_and_map_eq_of_slash_alGL_inv`](thm.html#ModularForm.exists_map_eq_qExpansion_smul_trace_mul_pow_and_map_eq_of_slash_alGL_inv).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_SlashInvariantForm_coe_trace_gammaH_eq_add_heckeU_slash_alGL_inv.lean

import Mathlib
import Definitions.Def_CohCarrier_Level
import Definitions.Def_ModularForm_HeckeOperator
import Definitions.Def_ModularForm_AtkinLehnerDatum

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups ModularForm

theorem SlashInvariantForm.coe_trace_gammaH_eq_add_heckeU_slash_alGL_inv
    {M p : ℕ} [NeZero M] (hp : p.Prime) (W : ModularForm.AtkinLehnerDatum M p)
    (H : Subgroup (ZMod M)ˣ)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Dvd.intro_left p W.hM.symm) u = 1 → u ∈ H)
    [((CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ))).IsFiniteRelIndex
      (CohCarrier.GammaH W.R (H.map (ZMod.unitsMap (Dvd.intro_left p W.hM.symm))) : Subgroup (GL (Fin 2) ℝ))]
    {k : ℤ} {F : Type*} [FunLike F UpperHalfPlane ℂ]
    [SlashInvariantFormClass F (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)) k] (f : F) :
    (⇑(SlashInvariantForm.trace
        (CohCarrier.GammaH W.R (H.map (ZMod.unitsMap (Dvd.intro_left p W.hM.symm))) : Subgroup (GL (Fin 2) ℝ)) f) :
        UpperHalfPlane → ℂ) =
      ⇑f + ModularForm.heckeU k p ((⇑f : UpperHalfPlane → ℂ) ∣[k] W.alGL⁻¹) := by sorry
