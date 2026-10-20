-- Prove2me | Theorems.Thm_SoficGroups_KunRootedWordPower_eventually_normalizedIndicatorDefect_markov_pow_lt_of_rooted
-- name    : SoficGroups.KunRootedWordPower.eventually_normalizedIndicatorDefect_markov_pow_lt_of_rooted
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:26.206993+00:00
-- url     : https://prove2.me/theorems/7e3ce47b-55a6-49f6-abc0-c448862fd93f
-- title:
--   SoficGroups.KunRootedWordPower.eventually_normalizedIndicatorDefect_markov_pow_lt_of_rooted
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

theorem SoficGroups.KunRootedWordPower.eventually_normalizedIndicatorDefect_markov_pow_lt_of_rooted
    {G : Type u} [Group G]
    (P : SoficGroups.KazhdanPair.{u, u} G)
    (S : Finset G) (honeS : 1 ∈ S)
    (hcover : P.generators ⊆ S)
    (hsymmetric : ∀ g ∈ S, g⁻¹ ∈ S)
    {V : ℕ → Type u} [∀ n, Fintype (V n)]
    (p : ∀ n, ↥S → Equiv.Perm (V n))
    (f : ∀ n, V n → ℝ)
    (σ : ∀ n, G → Equiv.Perm (V n))
    (w : G → List ↥S)
    (hf : ∀ n x, f n x = 0 ∨ f n x = 1)
    (hdefect : ∀ n,
      permutationMarkov (p n) (indicatorVector (f n)) ≠
        indicatorVector (f n))
    (hw : ∀ n g, σ n g = ((w g).map (p n)).prod)
    (hone : ∀ n, σ n 1 = 1)
    (hgenerator : ∀ n (i : ↥S), σ n (i : G) = p n i)
    (hroot : ∀ a g : G, ∀ᶠ n in Filter.atTop,
      ∀ x : V n, indicatorVector (f n) x ≠ 0 →
        σ n (a * g) x = (σ n a * σ n g) x)
    (k : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n in (Filter.hyperfilter ℕ : Filter ℕ),
      ‖((permutationMarkov (p n))^[k])
          (normalizedIndicatorDefect (p n) (f n))‖ <
        kazhdanMarkovContractionFactor P S ^ k + ε := by sorry
