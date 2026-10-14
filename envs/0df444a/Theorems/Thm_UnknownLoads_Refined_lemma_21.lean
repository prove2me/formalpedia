-- Prove2me | Theorems.Thm_UnknownLoads_Refined_lemma_21
-- name    : UnknownLoads.Refined.lemma_21
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T22:35:09.034894+00:00
-- url     : https://prove2.me/theorems/ee8745ba-108d-4217-bb7d-d668808a9263
-- title:
--   Lemma 21 — every x ∈ L^ε_M is within 4ε of some y ∈ L_M
-- statement:
--   Let $T\in\mathbb R$, $M\ge0$ and $\varepsilon\in\mathbb R$. Let $x$ be a real càdlàg function on $[0,T]$ with $x(0)=0$ and $|x(t)-x(s)|\le M|t-s|+\varepsilon$ for all $s,t\in[0,T]$ (that is, $x\in L^\varepsilon_M$). Then there is a càdlàg $y$ on $[0,T]$ with $y(0)=0$ and $|y(t)-y(s)|\le M|t-s|$ for all $s,t\in[0,T]$ ($y\in L_M$) such that
--   $$
--   \|x-y\|_T=\sup_{t\in[0,T]}|x(t)-y(t)|\le4\varepsilon .
--   $$
--
--   Combined with the compactness of $L_M$ (Arzelà–Ascoli), this turns approximate Lipschitz bounds into relative compactness; it is used in the proof of Proposition 4.
--
--   **Formalization Note** $M\ge0$ is added (the paper uses $L_{M_i}$ with $M_i>0$; for $M<0$ the set $L_M$ is empty when $T>0$). The sup-norm bound is stated pointwise on $[0,T]$.
-- source:
--   Goldsztajn, Borst & van Leeuwaarden, Learning and balancing unknown loads in large-scale systems, arXiv:2012.10142v3, p. 47, Lemma 21 (restatement of Bramson 1998, Lemma 4.2)

import Mathlib
import Definitions.Def_UnknownLoads_Refined_Load

open MeasureTheory ProbabilityTheory Set Filter Topology

namespace UnknownLoads.Refined

theorem lemma_21 (T M ε : ℝ) (hM : 0 ≤ M) (x : ℝ → ℝ) (hx : LipSet T M ε x) :
    ∃ y : ℝ → ℝ, LipSet T M 0 y ∧ ∀ t ∈ Icc 0 T, |x t - y t| ≤ 4 * ε := by sorry

end UnknownLoads.Refined
