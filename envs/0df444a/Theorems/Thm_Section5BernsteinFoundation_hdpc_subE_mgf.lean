-- Prove2me | Theorems.Thm_Section5BernsteinFoundation_hdpc_subE_mgf
-- name    : Section5BernsteinFoundation.hdpc_subE_mgf
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T19:04:00.388639+00:00
-- url     : https://prove2.me/theorems/c2dd9457-1e5a-575b-954c-6c3d1296426b
-- title:
--   Fixed-scale moment-generating-function bound for a centered subexponential variable
-- statement:
--   Let $(\Omega,\mathcal F,P)$ be a probability space and let $Y:\Omega\to\mathbb R$ be measurable with $\mathbb E_P[Y]=0$. Let $s>0$, assume $e^{|Y|/s}$ is integrable, and suppose $\mathbb E_P[e^{|Y|/s}]\le 2$. For every real $\lambda$ satisfying $|\lambda|s\le 1/2$, the random variable $e^{\lambda Y}$ is integrable and
--
--   $$
--   \mathbb E_P[e^{\lambda Y}]\le \exp(32\lambda^2s^2).
--   $$
--
--   This fixed-scale estimate supplies the moment-generating-function control used in Bernstein-type concentration bounds.
-- source:
--   Fixed-scale Bernstein MGF argument by Nickrobbins95, Prove2Me theorem ffb81651-cac7-4739-85c2-9cb4b69885be, accepted submission 997bda66-5ba4-4af2-8457-558693e93561; attribution recorded in Solutions/Section5BernsteinFoundation.lean, lines 3–6. Exact auxiliary formalization: Section5BernsteinFoundation.hdpc_subE_mgf, Solutions/Section5BernsteinFoundation.lean, lines 38–97. Used in the Section 5 formalization associated with https://arxiv.org/html/2609.40331v3; this is an auxiliary concentration result, not a separately numbered claim of that paper.

import Mathlib
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Real Filter Topology
namespace Section5BernsteinFoundation
end Section5BernsteinFoundation
open Section5BernsteinFoundation

theorem Section5BernsteinFoundation.hdpc_subE_mgf {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : Ω → ℝ) (hY : Measurable Y) (hmean : ∫ ω, Y ω ∂P = 0) (s : ℝ) (hs : 0 < s)
    (hint : Integrable (fun ω => exp (|Y ω| / s)) P)
    (hle : ∫ ω, exp (|Y ω| / s) ∂P ≤ 2) (l : ℝ) (hl : |l| * s ≤ 1 / 2) :
    Integrable (fun ω => exp (l * Y ω)) P ∧ mgf Y P l ≤ exp (32 * l ^ 2 * s ^ 2) := by sorry
