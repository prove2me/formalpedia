-- Prove2me | Theorems.Thm_PathORAMCap_lemma_4_16
-- name    : PathORAMCap.lemma_4_16
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:48:37.96205+00:00
-- url     : https://prove2.me/theorems/6bfb069a-2408-442f-9582-e4618acbf850
-- title:
--   Lemma 4.16 — scaled child-arrival gaps $\Gamma_v$ are i.i.d. $\mathrm{Exp}(1)$ and independent of $E_\varepsilon$
-- statement:
--   Let a complete binary tree have depth $\ell\ge1$ and assign independent $\mathrm{Exp}(\rho)$ variables $E_y$ to its leaves, $\rho>0$. For each node $v$ let $E_v$ be the minimum of the $E_y$ over the leaves below $v$. For every internal node $v$ put
--
--   $$r_v=\rho\,2^{\ell-|v|-1},\qquad \Gamma_v=r_v\,|E_{v0}-E_{v1}|.$$
--
--   Then
--
--   1. the variables $\Gamma_v$ are jointly independent;
--   2. each $\Gamma_v$ has law $\mathrm{Exp}(1)$;
--   3. the whole vector $(\Gamma_v)_v$ is independent of $E_\varepsilon$.
--
--   This identifies the joint law of the scaled waiting intervals in the comparison with geometric loads.
--
--   **Formalization Note** Internal nodes are the bit strings of length below $\ell$. $\mathrm{Exp}(\rho)$ is Mathlib's `expMeasure ρ`; the laws are given as pushforwards of the underlying probability measure.
--
--   Differences from the source:
--
--   - encoding: E_v, the minimum over the descendant leaves of v → the infimum of E_y over the leaves y with v ⪯ y; reason: the set of such leaves is finite and nonempty for every node of the tree, so the infimum is the minimum
-- source:
--   Chang, Au, The Minimum Bucket Capacity for Reliable Path ORAM, STOC 2027 submission (manuscript sha256 1762f048…), Lemma 4.16, p.28 (PDF p.31)

import Mathlib
import Definitions.Def_PathORAMCap_Leaf

set_option autoImplicit false

open MeasureTheory ProbabilityTheory

namespace PathORAMCap

/-- **Lemma 4.16** (Dyadic Exponential Gaps; Chang, Au, *The Minimum Bucket Capacity for Reliable Path ORAM*, STOC 2027 submission (manuscript sha256 1762f048…), p.28 (PDF p.31)): "Let a finite complete binary
tree have depth ℓ ≥ 1, and assign independent Exp(ρ) variables Ey to its leaves, for a common ρ > 0.
For each node v, let Ev be the minimum of these variables in its descendant leaves. For every internal
node, define rv = ρ 2^(ℓ−|v|−1), Γv = rv|Ev0 − Ev1|. The variables Γv are jointly independent with law
Exp(1), and their entire vector is independent of Eε."

**Formalization Note.** Leaves are `Leaf ℓ`; internal nodes are the bit strings of length `k < ℓ`,
indexed by `Σ k : Fin ℓ, Leaf k`. `E_v` is the infimum of `E_y` over the leaves `y ⪰ v` (a minimum
over a nonempty finite set for every node used). `Exp(ρ)` is Mathlib's `expMeasure ρ`. -/
theorem lemma_4_16 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (ρ : ℝ) (hρ : 0 < ρ) (E : Leaf ℓ → Ω → ℝ)
    (hind : iIndepFun E P) (hlaw : ∀ y, P.map (E y) = expMeasure ρ) :
    let Emin : List Bool → Ω → ℝ := fun v ω => ⨅ y : {y : Leaf ℓ // v <+: y.toList}, E y.1 ω
    let Γ : (Σ k : Fin ℓ, Leaf k) → Ω → ℝ := fun v ω =>
      ρ * 2 ^ (ℓ - v.1.val - 1) *
        |Emin (v.2.toList ++ [false]) ω - Emin (v.2.toList ++ [true]) ω|
    iIndepFun Γ P ∧ (∀ v, P.map (Γ v) = expMeasure 1) ∧
      IndepFun (fun ω v => Γ v ω) (Emin []) P := by sorry

end PathORAMCap
