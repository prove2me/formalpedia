-- Prove2me | Theorems.Thm_StochApproxDyn_WeakAPT_Supplement_tubeDist_expansion
-- name    : StochApproxDyn.WeakAPT.Supplement.tubeDist_expansion
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T19:17:26.809889+00:00
-- url     : https://prove2.me/theorems/04aeb46b-ceee-429c-9a70-b37b306968a0
-- title:
--   Lemma 9.3 (corrected: tubular boundary) — distance to S expands under Φ_T near Γ
-- statement:
--   Assume the standing assumptions of §9: $F$ generates the flow $\Phi$ on $\mathbb R^m$, $S$ is an embedded $(m-d)$-dimensional submanifold ($1\le d\le m$), $\Gamma\subseteq S$ is nonempty, compact and invariant, $S$ is locally invariant near $\Gamma$ (neighbourhood $U$, time $t_0$), and $\mathbb R^m=T_pS\oplus E^u_p$ over $\Gamma$ with $E^u$ continuous, invariant and uniformly exponentially expanded by $D\Phi_t$. Let $F$ and $S$ be of class $C^r$, $r\ge1$. Let $T$, $N$, the continuous extension $E^u$ to $N$, the smooth bundle $\tilde E^u$, $\varepsilon$, $N_0$ and $\Pi$ be chosen as in step 1 of §9.1 (pp. 50–51), let $f=\Phi_T$ and $V(x)=\|x-\Pi(x)\|$ on $N_0$.
--
--   Then there exist a neighbourhood $N_1\subseteq N_0$ of $\Gamma$ and $\rho>1$ such that for all $x\in N_1$, $f(x)\in N_0$ and
--
--   $$V(f(x))\ge\rho\,V(x).$$
--
--   This is the first step towards the Lyapounov function $\eta$ of Proposition 9.5, which increases exponentially along trajectories off $S$.
--
--   **Formalization Note** The construction is the predicate `IsTubularConstruction` listing the properties of the choices made on pp. 50–51, so the lemma is stated for every admissible choice. The projection $\Pi$ is named `Pr` in Lean.
--
--   Differences from the source:
--   - generalization: $F$ and $S$ smooth (standing assumption, p. 47) → $F$ and $S$ of class $C^r$ for some $r\ge1$ (including $r=\infty$); reason: smooth is the case $r=\infty$, and the paper itself works with $C^r$ and $C^{1+\alpha}$ data in Proposition 9.5 and Theorem 9.1.
--   - reading: "for all $x\in N_1$, $V(f(x))\ge\rho V(x)$" → also $f(x)\in N_0$; reason: $V$ is defined on $N_0$ only, so the printed inequality presupposes it.
--   - correction: the choices of step 1, made "small enough" in the text → the explicit list of properties of `IsTubularConstruction`, with $N_0$ an open neighbourhood of $S\cap\operatorname{int}N$ inside $N$ and $\mathbb R^m=T_pS\oplus E^u_p$ on $N\cap S$; reason: the printed "$N_0\subset N$ open neighbourhood of $S\cap N$" is impossible when $S$ meets $\partial N$, and $P_p$ is used on $N\cap S$.
-- source:
--   Benaïm, Dynamics of Stochastic Approximation Algorithms, Séminaire de Probabilités XXXIII, LNM 1709 (1999), p. 51, Lemma 9.3 (construction of §9.1 step 1, pp. 50–51; standing assumptions of §9, pp. 47–48)

import Mathlib
import Definitions.Def_StochApproxDyn_WeakAPT_Supplement_NormallyRepelling

open Filter
open scoped NNReal Topology

namespace StochApproxDyn.WeakAPT.Supplement

/-- Lemma 9.3 (Benaïm 1999, p. 51). In the setting of §9, with `F` and `S` of class `C^r`
(`r ≥ 1`), let `T, N, E^u, Ẽ^u, ε, N₀, Π` be chosen as in the construction of §9.1, step 1
(pp. 50–51), `f = Φ_T` and `V(x) = ‖x − Π(x)‖`. There exist a neighbourhood `N₁ ⊆ N₀` of `Γ` and
`ρ > 1` such that for all `x ∈ N₁`, `V(f(x)) ≥ ρ V(x)` (in particular `f(x) ∈ N₀`, where `V` is
defined). Here `Pr` is the projection `Π`. -/
theorem tubeDist_expansion {m d : ℕ} (r : ℕ∞) (hr : 1 ≤ r)
    (F : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m)) (hF : ContDiff ℝ (r : WithTop ℕ∞) F)
    (Φ : Flow ℝ (EuclideanSpace ℝ (Fin m))) (S Γ U : Set (EuclideanSpace ℝ (Fin m))) (t₀ : ℝ)
    (hS : IsSubmanifoldOfClass r d S)
    (Eu : EuclideanSpace ℝ (Fin m) → Submodule ℝ (EuclideanSpace ℝ (Fin m)))
    (hNR : IsNormallyRepellingSet d F Φ S Γ U t₀ Eu) (T : ℝ) (N : Set (EuclideanSpace ℝ (Fin m)))
    (Eext Et : EuclideanSpace ℝ (Fin m) → Submodule ℝ (EuclideanSpace ℝ (Fin m))) (ε : ℝ)
    (N₀ : Set (EuclideanSpace ℝ (Fin m)))
    (Pr : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m))
    (hC : IsTubularConstruction d Φ S Γ U Eu T N Eext Et ε N₀ Pr) :
    ∃ N₁ ∈ 𝓝ˢ Γ, N₁ ⊆ N₀ ∧ ∃ ρ : ℝ, 1 < ρ ∧ ∀ x ∈ N₁,
      Φ T x ∈ N₀ ∧ ρ * tubeDist Pr x ≤ tubeDist Pr (Φ T x) := by sorry

end StochApproxDyn.WeakAPT.Supplement
