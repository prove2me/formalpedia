-- Prove2me | Theorems.Thm_RobustLS_LinFrac_sdp_upper_bound_theorem52
-- name    : RobustLS.LinFrac.sdp_upper_bound_theorem52
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T13:41:01.394309+00:00
-- url     : https://prove2.me/theorems/a10ccf87-d453-4ec8-a482-bf27b3fb9d93
-- title:
--   Theorem 5.2 (corrected) — the SDP (40) upper-bounds the linear-fractional worst-case residual, exactly when 𝒟 = ℝ^{N×N}
-- statement:
--   Consider the linear-fractional robust least-squares model of §5.2 with $\rho = 1$: a subspace $\mathcal D \subseteq \mathbb R^{N\times N}$, data $A \in \mathbb R^{n\times m}$, $b \in \mathbb R^n$, $L \in \mathbb R^{n\times N}$, $R_A \in \mathbb R^{N\times m}$, $R_b \in \mathbb R^N$, $D \in \mathbb R^{N\times N}$, the perturbed data $A(\Delta) = A + L\Delta(I - D\Delta)^{-1}R_A$, $b(\Delta) = b + L\Delta(I - D\Delta)^{-1}R_b$, and the worst-case residual
--
--   $$
--   r_{\mathcal D}(A,b,x) = \max_{\Delta \in \mathcal D,\ \|\Delta\| \le 1} \|A(\Delta)x - b(\Delta)\| \quad (\text{$= +\infty$ if $\det(I - D\Delta) = 0$ for some such $\Delta$}).
--   $$
--
--   Let $\mathcal S$, $\mathcal G$ be the symmetric and skew-symmetric matrices commuting with every element of $\mathcal D$, and $\mathcal F(\lambda, S, G, x)$ the matrix (38)–(39). Consider the SDP
--
--   $$
--   \inf_{S, G, \lambda}\ \lambda \quad \text{subject to} \quad S \in \mathcal S,\ G \in \mathcal G,\ S \succ 0,\ G\Delta = -(G\Delta)^T \ \forall \Delta \in \mathcal D,\ \mathcal F(\lambda, S, G, x) \succ 0 . \qquad (40)
--   $$
--
--   Then, for every $x \in \mathbb R^m$ and $\lambda \in \mathbb R$:
--
--   1. **(Upper bound.)** If $(\lambda, S, G)$ is feasible for (40), then $\lambda > r_{\mathcal D}(A,b,x)$.
--   2. **(Exactness for full perturbations.)** If $\mathcal D = \mathbb R^{N\times N}$ and $\lambda > r_{\mathcal D}(A,b,x)$, then there is $s > 0$ such that $(\lambda, sI, 0)$ is feasible for (40).
--
--   Hence the value of (40) is an upper bound on $r_{\mathcal D}(A,b,x)$, and it equals $r_{\mathcal D}(A,b,x)$ when $\mathcal D = \mathbb R^{N\times N}$ (with (40) infeasible exactly when $r_{\mathcal D} = +\infty$).
--
--   Computing $r_{\mathcal D}$ is NP-hard in general (Lemma 5.1); this theorem replaces it by a polynomial-time computable bound that is tight for unstructured perturbations.
--
--   **Formalization Note** The printed (40) has only $S \in \mathcal S$, $G \in \mathcal G$ and (38); the constraints $S \succ 0$ (from Lemma 2.3's hypotheses) and "$G\Delta$ skew-symmetric for every $\Delta \in \mathcal D$" (the identity $p^TGq = 0$ of Lemma 2.3's proof) are added, because without either one the upper bound is false (counterexamples in the milestone for Eqs. (38)–(39)). Both hold for the exactness certificate $S = sI$, $G = 0$. The statement is written through $\lambda$'s feasibility rather than an infimum over the open LMI set: part 1 says every feasible $\lambda$ exceeds $r_{\mathcal D}$, part 2 that every $\lambda > r_{\mathcal D}$ is feasible. The printed last sentence, "If $\Theta > 0$ at the optimum, the upper bound is also exact", is not stated: the infimum over the strict inequality (38) is not attained, and the paper does not specify the limit it refers to. "$\lambda > r_{\mathcal D}$" is the predicate `ResidualBelow`.
-- source:
--   El Ghaoui & Lebret, Robust Solutions to Least-Squares Problems with Uncertain Data, SIAM J. Matrix Anal. Appl. 18(4):1035–1064 (1997), p. 1048, Theorem 5.2, Eq. (40) (corrected; last clause not stated); proof in Appendix C, pp. 1061–1062

import Mathlib
import Definitions.Def_RobustLS_LinFrac_Core

open Matrix

namespace RobustLS.LinFrac

/-- El Ghaoui & Lebret (1997), Theorem 5.2, p. 1048 (PDF p. 14), **corrected**, with `ρ = 1`.
Printed: "When ρ = 1, an upper bound on the worst-case residual r_𝒟(A, b, x) can be obtained by
solving the SDP (40) inf_{S,G,λ} λ subject to S ∈ 𝒮, G ∈ 𝒢, (38). The upper bound is exact when
𝒟 = ℝ^{N×N}."
(a) Upper bound: every `λ` feasible for (40) — with the added constraints `S ≻ 0` and `GΔ`
skew-symmetric for every `Δ ∈ 𝒟` (see `residualBelow_of_certificate` for the counterexamples
to the printed version) — satisfies `λ > r_𝒟(A, b, x)`.
(b) Exactness for `𝒟 = ℝ^{N×N}`: every `λ > r_𝒟(A, b, x)` is feasible for (40), already with
`S = sI` (`s > 0`) and `G = 0`, which lie in `𝒮`, `𝒢` and satisfy the added constraints.
Together, the infimum (40) equals `r_𝒟(A, b, x)` when `𝒟 = ℝ^{N×N}`, including `r_𝒟 = ∞`
exactly when (40) is infeasible. The printed clause "If Θ > 0 at the optimum, the upper bound is
also exact" is not stated (the infimum over the strict LMI (38) is not attained). -/
theorem sdp_upper_bound_theorem52 {n m N : ℕ} (𝒟 : Submodule ℝ (Matrix (Fin N) (Fin N) ℝ))
    (A : Matrix (Fin n) (Fin m) ℝ) (b : Fin n → ℝ) (L : Matrix (Fin n) (Fin N) ℝ)
    (RA : Matrix (Fin N) (Fin m) ℝ) (Rb : Fin N → ℝ) (D : Matrix (Fin N) (Fin N) ℝ)
    (x : Fin m → ℝ) (lam : ℝ) :
    (∀ S G : Matrix (Fin N) (Fin N) ℝ, S ∈ symCommutant 𝒟 → G ∈ skewCommutant 𝒟 →
        (∀ Δ ∈ 𝒟, (G * Δ)ᵀ = -(G * Δ)) → S.PosDef →
        (lmiF A b L RA Rb D x lam S G).PosDef → ResidualBelow 𝒟 A b L RA Rb D x lam) ∧
    (𝒟 = ⊤ → ResidualBelow 𝒟 A b L RA Rb D x lam →
        ∃ s : ℝ, 0 < s ∧ (lmiF A b L RA Rb D x lam (s • 1) 0).PosDef) := by sorry

end RobustLS.LinFrac
