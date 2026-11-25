-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_approxB_split
-- name    : ReciprocityTheory.MultiplicativeHeights.approxB_split
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T11:03:33.043951+00:00
-- url     : https://prove2.me/theorems/1eef4c03-68f0-5605-a874-8fd1977d4153
-- title:
--   Multiplicative Heights: approx B split
-- statement:
--   The Multiplicative Heights construction uses the approx B split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/ApproxBasisB.lean#L78-L211
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/ApproxBasisB.lean#L78-L211

import Definitions.Def_ReciprocityTheory_SemistableReduction_ApproxBasisA
import Definitions.Def_ReciprocityTheory_SemistableReduction_ApproxBasisB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open Matrix NumberField ComplexConjugate

theorem ReciprocityTheory.MultiplicativeHeights.approxB_split {K : Type} [Field K] [NumberField K] {r p : ℕ} (hp : p ≤ r) (S : HermForm K r)
    (L : Submodule (𝓞 K) (Fin r → K)) (hL : IsIntegralOn S L) (l v : Fin r → Fin r → K)
    (hl : ∀ j, l j ∈ L) (hvi : LinearIndependent K v)
    (hinj : ∀ g : ApproxPosIdx r p → K,
      (∀ k : ApproxPosIdx r p, S.h (l k.1) (∑ j : ApproxPosIdx r p, g j • l j.1) = 0) → g = 0) :
    ∃ (Δ : K) (coef : (Fin r → K) → ApproxPosIdx r p → K) (a : {j : Fin r // ¬ (j : ℕ) < p} → Fin r),
      Δ ≠ 0 ∧ Δ = (Matrix.of fun k j : ApproxPosIdx r p => S.h (l k.1) (l j.1)).det ∧
      (∀ x (k : ApproxPosIdx r p), S.h (l k.1) (Δ • x - ∑ k', coef x k' • l k'.1) = 0) ∧
      (∀ x ∈ L, Δ • x - ∑ k', coef x k' • l k'.1 ∈ L) ∧
      LinearIndependent K (fun j : Fin r => if h : (j : ℕ) < p then l j else
        Δ • v (a ⟨j, h⟩) - ∑ k', coef (v (a ⟨j, h⟩)) k' • l k'.1) := by sorry
