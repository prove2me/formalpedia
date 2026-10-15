-- Prove2me | Theorems.Thm_PiIrrationality_Bai_final_numeric
-- name    : PiIrrationality.Bai.final_numeric
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-10-14T19:57:46.804129+00:00
-- url     : https://prove2.me/theorems/05f5a212-97e7-4a32-aeeb-03e248d0534e
-- title:
--   Numerical endgame for Bai's bound $1+s/t\le 7.101862832357$
-- statement:
--   For $\omega\in[1202.565773361291,1203]$, $0\le\delta\le10^{-16}$ and the rates
--   $$s=7430-929\log 2-\omega+\log 25+15979.97420422751+10^5\delta,$$
--   $$t=6542.209753096835-(7430-4645\log 2-\omega)-10^5\delta,\quad g=6542.209753096835+3716\log 2+\log 25+15979.974204227497-10^5\delta,$$
--   one has $0<s$, $0<t$, $s<g$, $1+s/t\le 7.101862832357$ and $1+s/(g-s)\le 7.101862832357$.
--
--   Role: the final inequality (5.22)-(5.23) of Bai with every constant certified.
-- source:
--   Y. Bai, The irrationality measure of π is at most 7.101862832357, arXiv:2609.11276 (v2, 11 Sep 2026), https://arxiv.org/abs/2609.11276, (5.14)-(5.23)

import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem PiIrrationality.Bai.final_numeric (ω δ s t g : ℝ) (hω : 1202.565773361291 ≤ ω) (hω' : ω ≤ 1203)
    (hδ : 0 ≤ δ) (hδ' : δ ≤ 1e-16)
    (hs : s = 7430 - 929 * Real.log 2 - ω + Real.log 25 + 15979.97420422751 + 100000 * δ)
    (ht : t = 6542.209753096835 - (7430 - 4645 * Real.log 2 - ω) - 100000 * δ)
    (hg : g = 6542.209753096835 + 3716 * Real.log 2 + Real.log 25 + 15979.974204227497 - 100000 * δ) :
    0 < s ∧ 0 < t ∧ s < g ∧ 1 + s / t ≤ 7.101862832357 ∧ 1 + s / (g - s) ≤ 7.101862832357 := by
  sorry
