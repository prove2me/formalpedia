-- Prove2me | Theorems.Thm_SoficGroups_KunRootedWordPower_tendsto_norm_normalizedIndicatorDefect_markov_pow
-- name    : SoficGroups.KunRootedWordPower.tendsto_norm_normalizedIndicatorDefect_markov_pow
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:25.142856+00:00
-- url     : https://prove2.me/theorems/3708db5f-378a-4f1d-a55a-26a343c6354d
-- title:
--   SoficGroups.KunRootedWordPower.tendsto_norm_normalizedIndicatorDefect_markov_pow
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunRootedWordPower
open Filter Topology
open SoficGroups.KunRootedIndicatorCrossing
open SoficGroups.KunThomInvariantOrthogonal
open scoped BigOperators ComplexConjugate ComplexOrder InnerProductSpace Pointwise
universe u v w

theorem SoficGroups.KunRootedWordPower.tendsto_norm_normalizedIndicatorDefect_markov_pow
    {G ι H : Type*} [Group G] [Fintype ι] [Nonempty ι]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {V : ℕ → Type*} [∀ n, Fintype (V n)]
    (p : ∀ n, ι → Equiv.Perm (V n))
    (f : ∀ n, V n → ℝ)
    (σ : ∀ n, G → Equiv.Perm (V n))
    (s : ι → G)
    (v : G × G → H)
    (hone : ∀ n, σ n 1 = 1)
    (hgenerator : ∀ n i, σ n (s i) = p n i)
    (hroot : ∀ a g : G, ∀ᶠ n in Filter.atTop,
      ∀ x : V n, indicatorVector (f n) x ≠ 0 →
        σ n (a * g) x = (σ n a * σ n g) x)
    (hgram : ∀ q r,
      Tendsto
        (fun n =>
          ⟪normalizedPairDisplacement (p n) (f n) (σ n) q,
            normalizedPairDisplacement (p n) (f n) (σ n) r⟫_ℂ)
        (Filter.hyperfilter ℕ)
        (𝓝 ⟪v q, v r⟫_ℂ))
    (k : ℕ) :
    Tendsto
      (fun n =>
        ‖((permutationMarkov (p n))^[k])
          (normalizedIndicatorDefect (p n) (f n))‖)
      (Filter.hyperfilter ℕ)
      (𝓝 ‖pairedDefectWordAverage s v k‖) := by sorry
