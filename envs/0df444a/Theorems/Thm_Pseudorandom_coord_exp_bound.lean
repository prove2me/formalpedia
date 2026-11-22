-- Prove2me | Theorems.Thm_Pseudorandom_coord_exp_bound
-- name    : Pseudorandom.coord_exp_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:47:48.848678+00:00
-- url     : https://prove2.me/theorems/bad56334-5d3e-4a48-9f0a-0bb19384df37
-- title:
--   Pseudorandom: coord exp bound
-- statement:
--   One-coordinate exponential bound.
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/RequestProject/Pseudorandom/Bernstein.lean#L68-L155
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/RequestProject/Pseudorandom/Bernstein.lean#L68-L155

module
public import Definitions.Def_RequestProject_Pseudorandom_FiniteProb
public import Definitions.Def_RequestProject_Pseudorandom_Bernstein
set_option autoImplicit true
@[expose] public section
public section
open Pseudorandom
open Finset

theorem Pseudorandom.coord_exp_bound {α : Type*} [Fintype α] (p : α → ℝ) (hp0 : ∀ a, 0 ≤ p a)
    (hp1 : ∑ a, p a = 1) (M : α → ℝ) (c L lam q : ℝ) (R : Finset α)
    (hgap : ∀ a b, |M a - M b| ≤ c) (hR : ∀ a b, a ∉ R → b ∉ R → M a = M b)
    (hq : ∑ a ∈ R, p a ≤ q) (hcL : c ≤ L) (hlam : 0 ≤ lam) (hlamL : lam * L < 1) :
    ∑ a, p a * Real.exp (lam * (M a - ∑ b, p b * M b)) ≤
      Real.exp (lam ^ 2 * (q * c ^ 2) / (2 * (1 - lam * L))) := by sorry
