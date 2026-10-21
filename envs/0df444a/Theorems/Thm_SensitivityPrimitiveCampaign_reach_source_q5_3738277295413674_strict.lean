-- Prove2me | Theorems.Thm_SensitivityPrimitiveCampaign_reach_source_q5_3738277295413674_strict
-- name    : SensitivityPrimitiveCampaign.reach_source_q5_3738277295413674_strict
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-20T22:35:12.903461+00:00
-- url     : https://prove2.me/theorems/01bb63ef-ced2-4ae9-8b81-b5ed295526c6
-- title:
--   Six shared defect tolerances improve the sensitivity exponent to 2.1308255794
-- statement:
--   Let $s(f)$ and $\operatorname{bs}(f)$ denote sensitivity and block sensitivity of a finite Boolean function. Set
--
--   $$\alpha=\frac{\log(14055^8)}{\log(3738277295413674)}=2.1308255793978239476\ldots.$$
--
--   For every $\varepsilon>0$ and every integer $S\ge2$, there are an integer $n$ and a Boolean function $f:\{0,1\}^n\to\{0,1\}$ with
--
--   $$s(f)\ge S,\qquad \operatorname{bs}(f)\ge s(f)^{\alpha-\varepsilon}.$$
--
--   Moreover,
--
--   $$\frac{\log(14055^8)}{\log(3738289747988852)}<\alpha.$$
--
--   This strictly improves the five-tolerance source profile by more than $1.9795\times10^{-7}$ and the earlier public exponent $2.1303203332203658\ldots$ by more than $0.000505246$. The construction uses a single binary tournament labeling with ordinary defect cutoffs $(24,31,38,44,50,55)$ and source cutoff $22$, followed by an exact recursive Boolean profile.
--
--   The formal statement spells out both quantities using finite sets: sensitivity is the maximum number of changing singleton coordinates, and block sensitivity is the maximum number of pairwise disjoint nonempty changing blocks. These are the same primitive definitions used in the sensitivity campaign; this self-contained statement requires only Mathlib. No optimality assertion is made.
-- source:
--   Strictly improves the five-tolerance source endpoint log(14055^8)/log(3738289747988852) and https://prove2.me/theorems/62961329-4b50-48c7-a1fd-11159da9de26. Uses the same exact finite sensitivity and block-sensitivity definitions as public definitions SensitivitySeparation and SensitivityCampaign. Attribution to Robin Kothari and the earlier OpenAI sensitivity and local-lemma development is retained in the proof source.

module

public import Mathlib

@[expose] public section
open scoped Classical
set_option autoImplicit false

theorem SensitivityPrimitiveCampaign.reach_source_q5_3738277295413674_strict :
  (∀ ε : ℝ, 0 < ε → ∀ S : ℕ, 2 ≤ S →
    ∃ (n : ℕ) (f : (Fin n → Bool) → Bool),
      let flipBits : (Fin n → Bool) → Finset (Fin n) → (Fin n → Bool) :=
        fun x B i => if i ∈ B then !(x i) else x i
      let s : ℕ := Finset.univ.sup (fun x : Fin n → Bool =>
        (Finset.univ.filter fun i : Fin n => f (flipBits x {i}) ≠ f x).card)
      let bs : ℕ := Finset.univ.sup (fun x : Fin n → Bool =>
        Finset.univ.sup (fun blocks : Finset (Finset (Fin n)) =>
          if (∀ A ∈ blocks, ∀ B ∈ blocks, A ≠ B → Disjoint A B) ∧
              (∀ B ∈ blocks, B.Nonempty ∧ f (flipBits x B) ≠ f x)
          then blocks.card else 0))
      S ≤ s ∧ (s : ℝ) ^ ((Real.log (1522813785050025472152230187890625 : ℝ) / Real.log (3738277295413674 : ℝ)) - ε) ≤ (bs : ℝ)) ∧
  (Real.log (1522813785050025472152230187890625 : ℝ) /
      Real.log (3738289747988852 : ℝ) < (Real.log (1522813785050025472152230187890625 : ℝ) / Real.log (3738277295413674 : ℝ))) := by sorry
