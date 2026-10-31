-- Prove2me | Theorems.Thm_RobustToDynamics_rho_star_steps_to_convergence
-- name    : RobustToDynamics.rho_star_steps_to_convergence
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:37:45.178502+00:00
-- url     : https://prove2.me/theorems/52b6bf6b-fa38-4b75-97da-53deff2d0dca
-- title:
--   Solving R-LD-LP — for $\rho(G)\le\rho^*<1$: $\rho(\hat G)<1$, shrinkage $\hat\rho^2$, and $\mathcal S=\mathcal S_r$ with $r=\lceil\log(\hat\alpha_2/\hat\alpha_1)/\log(1/\hat\rho^2)\rceil$
-- statement:
--   Let $\rho^*<1$ and $G\in\mathbb R^{n\times n}$ with $\rho(G)\le\rho^*$. Put
--   $$
--   \hat\rho=\frac{1+\rho^*}{2},\qquad \hat G=\frac1{\hat\rho}\,G .
--   $$
--   Let $A\in\mathbb R^{m\times n}$, $b\in\mathbb R^m$ with the origin in the interior of $P=\{x: Ax\le b\}$, let $\hat M$ solve $\hat G^T\hat M\hat G-\hat M=-I$, and let $l,u$ be box bounds with $P\subseteq\{x: l\le x\le u\}$. Then
--
--   1. $\rho(\hat G)<1$;
--   2. $\hat\rho^2\hat M-G^T\hat MG$ is positive definite, i.e. $\hat M\succ\frac1{\hat\rho^2}G^T\hat MG$, which gives the shrinkage factor $\hat\gamma=\hat\rho^2$;
--   3. with $\hat\alpha_1,\hat\alpha_2$ from (2.15), (2.16) for $\hat M$ and
--   $$
--   r=\left\lceil\frac{\log(\hat\alpha_2/\hat\alpha_1)}{\log(1/\hat\gamma)}\right\rceil,
--   $$
--   $\mathcal S=\mathcal S_r$.
--
--   Since $\hat\gamma$ depends only on the fixed $\rho^*$, this $r$ is polynomially bounded, which yields the second claim of Theorem 2.7.
--
--   Differences from the source:
--   - generalization: a fixed rational ρ* < 1 → any real ρ* < 1; reason: the rational case is a special case; ρ* < 0 admits no G since ρ(G) ≥ 0
--   - reading: the hypotheses P bounded and 0 ∈ int P of Theorem 2.7 → 0 ∈ int P and a box P ⊆ [l, u]; reason: the step reuses (2.15) and (2.16), which need both; the source states them once in the theorem's If-clause
--   - generalization: l_i, u_i the minimum and maximum of x_i over P (P bounded) → any l, u with P ⊆ [l, u] (which forces P bounded, so no separate boundedness hypothesis); reason: the paper's coordinatewise LP bounds are one such box
--   - encoding: M̂ ≻ (1/ρ̂²) GᵀM̂G → (ρ̂² M̂ − GᵀM̂G).PosDef; reason: multiplying by ρ̂² > 0 preserves the strict Loewner order
--   - encoding: r = ⌈·⌉, a nonnegative integer → Nat.ceil (a negative argument gives 0); reason: S_r is defined for integers r ≥ 0, and S = S_0 = P whenever the ratio makes the ceiling nonpositive
--   - generalization: rational data → real data; reason: the statement for real matrices specializes to rational ones by casting
--   - encoding: ρ(G) = max of |λ| over the (real or complex) eigenvalues → specRadius, the supremum of |z| over the complex spectrum; reason: the complex spectrum of an n × n matrix is finite and nonempty for n ≥ 1, so the supremum is the maximum; same value
-- source:
--   Ahmadi & Günlük, Robust-to-Dynamics Optimization, arXiv:1805.03682v2, Theorem 2.7, proof, "Solving R-LD-LP in polynomial time", p.16

import Mathlib
import Definitions.Def_RobustToDynamics_specRadius
import Definitions.Def_RobustToDynamics_polyhedron
import Definitions.Def_RobustToDynamics_feasibleSet
import Definitions.Def_RobustToDynamics_outerApprox
import Definitions.Def_RobustToDynamics_alpha1
import Definitions.Def_RobustToDynamics_alpha2

open Matrix

namespace RobustToDynamics

/-- **Solving R-LD-LP: with `ρ(G) ≤ ρ*`, the shrinkage factor `ρ̂²` and `S = S_r`.**
Ahmadi & Günlük, *Robust-to-Dynamics Optimization*, arXiv:1805.03682v2, Theorem 2.7, proof,
"Solving R-LD-LP in polynomial time", p.16: "we now solve the Lyapunov equation ĜT M̂ Ĝ − M̂ = −I,
where Ĝ = (1/ρ̂)G and ρ̂ = (1 + ρ∗)/2. As ρ(G) < ρ̂ < 1, we have ρ(Ĝ) < 1 … M̂ ≻ ĜT M̂ Ĝ =
(1/ρ̂2) GT M̂ G which readily gives the shrinkage factor γ̂ = ρ̂2. … with
r = ⌈log(α̂2/α̂1) / log(1/γ̂)⌉, we must have S = Sr."

Let `ρ* < 1`, `ρ(G) ≤ ρ*`, `ρ̂ = (1 + ρ*)/2` and `Ĝ = (1/ρ̂)G`; let the origin lie in the interior
of `P = {x | Ax ≤ b}`, let `M̂` solve `ĜᵀM̂Ĝ − M̂ = −I`, and let `P ⊆ {x | l ≤ x ≤ u}`. Then
`ρ(Ĝ) < 1`, `ρ̂²M̂ − GᵀM̂G` is positive definite (so `GᵀM̂G ⪯ ρ̂²M̂`), and with `α̂₁, α̂₂` from
(2.15), (2.16) for `M̂` and `r = ⌈log(α̂₂/α̂₁)/log(1/ρ̂²)⌉`, `S = S_r`.

**Formalization Note.** `ρ*` is real (a generalization of the paper's rational `ρ*`); `ρ* < 0`
admits no `G`, since `specRadius G ≥ 0`. `⌈·⌉₊` is `Nat.ceil`. `l, u` are any box bounds with
`P ⊆ [l, u]` (the paper's coordinatewise LP minima and maxima are one choice; the box forces `P`
bounded). The strict form `M̂ ≻ (1/ρ̂²)GᵀM̂G` is stated as positive definiteness of
`ρ̂²M̂ − GᵀM̂G`. -/
theorem rho_star_steps_to_convergence {m n : ℕ} (ρstar : ℝ) (hρ : ρstar < 1)
    (G : Matrix (Fin n) (Fin n) ℝ) (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (hG : specRadius G ≤ ρstar)
    (h0 : (0 : Fin n → ℝ) ∈ interior (polyhedron A b))
    (Mhat : Matrix (Fin n) (Fin n) ℝ)
    (hL : ((1 / ((1 + ρstar) / 2)) • G)ᵀ * Mhat * ((1 / ((1 + ρstar) / 2)) • G) - Mhat = -1)
    (l u : Fin n → ℝ) (hbox : polyhedron A b ⊆ Set.Icc l u) :
    specRadius ((1 / ((1 + ρstar) / 2)) • G) < 1 ∧
      (((1 + ρstar) / 2) ^ 2 • Mhat - Gᵀ * Mhat * G).PosDef ∧
      feasibleSet A b G = outerApprox A b G
        ⌈Real.log (alpha2 Mhat l u / alpha1 Mhat A b) / Real.log (1 / ((1 + ρstar) / 2) ^ 2)⌉₊ := by sorry

end RobustToDynamics
