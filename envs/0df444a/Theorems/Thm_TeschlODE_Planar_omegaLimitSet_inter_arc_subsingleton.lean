-- Prove2me | Theorems.Thm_TeschlODE_Planar_omegaLimitSet_inter_arc_subsingleton
-- name    : TeschlODE.Planar.omegaLimitSet_inter_arc_subsingleton
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T15:27:03.409011+00:00
-- url     : https://prove2.me/theorems/ebf06dfc-d1d1-4f70-9498-75de97e84f97
-- title:
--   Corollary 7.10 — ω_σ(x) meets a transversal arc in at most one point
-- statement:
--   Let $M \subseteq \mathbb{R}^2$ be open, $f \in C^1(M, \mathbb{R}^2)$, $x \in M$, $\sigma \in \{\pm\}$, and let $\Sigma$ be a transversal arc. Then
--   $$ \#\big(\omega_\sigma(x) \cap \Sigma\big) \le 1 .$$
--
--   **Formalization Note.** Stated as `Set.Subsingleton` of the intersection; $\sigma$ is a `Bool` (`true` = $+$).
-- source:
--   Teschl, Ordinary Differential Equations and Dynamical Systems (author's preliminary version of AMS GSM 140, 2012), p. 222, Corollary 7.10

import Mathlib
import Definitions.Def_TeschlODE_Planar_omegaLimitSet
import Definitions.Def_TeschlODE_Planar_IsTransversalArc

namespace TeschlODE.Planar

/-- Teschl, Corollary 7.10 (p. 222): for `M ⊆ ℝ²` open, `f ∈ C¹(M, ℝ²)`, `x ∈ M`, `σ ∈ {±}` and
a transversal arc `Σ = s(J)`, the limit set `ω_σ(x)` meets `Σ` in at most one point. -/
theorem omegaLimitSet_inter_arc_subsingleton {M : Set (Fin 2 → ℝ)} (hM : IsOpen M)
    {f : (Fin 2 → ℝ) → Fin 2 → ℝ} (hf : ContDiffOn ℝ 1 f M) (σ : Bool)
    {x : Fin 2 → ℝ} (hx : x ∈ M)
    {J : Set ℝ} {s : ℝ → Fin 2 → ℝ} (harc : IsTransversalArc f M J s) :
    (omegaLimitSet f M σ x ∩ s '' J).Subsingleton := by sorry

end TeschlODE.Planar
