-- Prove2me | Theorems.Thm_WeakMFG_Existence_theorem_7_5
-- name    : WeakMFG.Existence.theorem_7_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T23:12:41.417107+00:00
-- url     : https://prove2.me/theorems/e66db5f7-ccb3-48c0-96bb-080e9ab09f62
-- title:
--   Theorem 7.5 (Berge's Theorem) — the max value is continuous and the argmax is upper hemicontinuous and compact-valued
-- statement:
--   Let $E$ be a metric space, $K$ a nonempty compact metric space and $\phi:E\times K\to\mathbb R$ continuous. Then
--   $$\gamma(x):=\max_{y\in K}\phi(x,y)$$
--   is continuous, and the set-valued map
--   $$E\ni x\mapsto\arg\max_{y\in K}\phi(x,y):=\{y\in K:\gamma(x)=\phi(x,y)\}$$
--   is upper hemicontinuous and compact-valued.
--
--   This special case of Berge's maximum theorem gives the continuity of the maximized Hamiltonian and the upper hemicontinuity of the maximizer sets (Lemma 7.9).
--
--   **Formalization Note** $K$ is assumed nonempty, which the maximum requires; $\gamma$ is written as a supremum, which is attained for compact nonempty $K$. Upper hemicontinuity is the notion `UHCAt` of §7.1.
-- source:
--   Carmona, Lacker, A probabilistic weak formulation of mean field games and applications, arXiv:1307.1152v2 (2014), Theorem 7.5, p. 24 (Berge's Theorem; Aliprantis–Border 17.31)

import Mathlib
import Definitions.Def_WeakMFG_Existence_UHC

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal Matrix

namespace WeakMFG.Existence

/-- Theorem 7.5 (Berge's Theorem; Carmona–Lacker, arXiv:1307.1152v2, p. 24): let `E` be a metric
space, `K` a compact metric space and `φ : E × K → ℝ` continuous. Then `γ(x) := max_{y ∈ K} φ(x, y)`
is continuous, and `E ∋ x ↦ argmax_{y ∈ K} φ(x, y) := {y ∈ K : γ(x) = φ(x, y)}` is upper
hemicontinuous and compact-valued.
Formalization Note: `K` nonempty is added (the maximum needs it); `γ` is written as `⨆`, which
is a genuine maximum for compact nonempty `K`. -/
theorem theorem_7_5 {E K : Type*} [MetricSpace E] [MetricSpace K] [CompactSpace K] [Nonempty K]
    (φ : E × K → ℝ) (hφ : Continuous φ) :
    Continuous (fun x => ⨆ y, φ (x, y)) ∧
    ∀ x : E, UHCAt (fun x : E => {y : K | (⨆ y', φ (x, y')) = φ (x, y)}) x ∧
      IsCompact {y : K | (⨆ y', φ (x, y')) = φ (x, y)} := by sorry

end WeakMFG.Existence
