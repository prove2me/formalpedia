-- Prove2me | Theorems.Thm_SFLOracleLowerBound_Hardness_minimization_facts
-- name    : SFLOracleLowerBound.Hardness.minimization_facts
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T02:25:58.650602+00:00
-- url     : https://prove2.me/theorems/9dcd27a4-d73b-4e02-8922-285680db1583
-- title:
--   Lemma 6 — Minimization facts
-- statement:
--   For finite ground sets $E,W$, the following hold.
--
--   1. If $H:2^{E\sqcup W}\to\mathbb R$ is submodular, then $h_1$ is submodular.
--   2. If $\varphi:E\to W$ and $r:2^W\to\mathbb R_{\ge0}$ is normalized and submodular, then $h_2$ is normalized, monotone and submodular, with $h_2(S)\le|S|$. If $r$ is integer-valued, $h_2$ is a matroid rank function.
--
--   Here
--   $$h_1(S)=\min_{A\subseteq W}H(S\sqcup A),\qquad h_2(S)=\min_{A\subseteq W}(|S\setminus\varphi^{-1}(A)|+r(A)).$$
--   These closure facts support the replicated cost construction; $r$ need not be monotone.
--
--   Differences from the source:
--   - encoding: finite ground sets and their subsets → finite types and Finset subsets; reason: bijections preserve every subset, cardinality and set operation
--   - encoding: r has codomain ℝ≥0 → r is real-valued with explicit nonnegativity; reason: this represents exactly the same functions and exposes the sign assumption
-- source:
--   Adam N. Elmachtoub, Bento Natura, Meike Neuwohner, Settling the Approximability of Submodular Facility Location, STOC 2027 submission #1249 (October 2026), Lemma 6(i)–(ii), p.7; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1249.pdf

import Mathlib
import Definitions.Def_SFLOracleLowerBound_Hardness_SetFunctions

set_option autoImplicit false

noncomputable section

namespace SFLOracleLowerBound.Hardness

open Classical Finset MeasureTheory
open scoped ENNReal

/-- Lemma 6(i)–(ii), p.7. No monotonicity assumption on r. -/

theorem minimization_facts {E W : Type} [Fintype E] [Fintype W] [DecidableEq E] [DecidableEq W] :
    (∀ H : Finset (Sum E W) → ℝ, NonmonotoneSubmod.Shared.Submodular H →
      NonmonotoneSubmod.Shared.Submodular (partialMinimum H)) ∧
    (∀ (φ : E → W) (r : Finset W → ℝ), (∀ A, 0 ≤ r A) → Normalized r →
      NonmonotoneSubmod.Shared.Submodular r →
      FacilityCost (pullbackMinimum φ r) ∧
      (∀ S, pullbackMinimum φ r S ≤ S.card) ∧
      (IntegerValued r → MatroidRank (pullbackMinimum φ r))) := by sorry

end SFLOracleLowerBound.Hardness
