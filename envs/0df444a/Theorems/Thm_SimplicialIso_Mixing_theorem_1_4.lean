-- Prove2me | Theorems.Thm_SimplicialIso_Mixing_theorem_1_4
-- name    : SimplicialIso.Mixing.theorem_1_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T07:24:00.172987+00:00
-- url     : https://prove2.me/theorems/4b72439b-e325-4e03-8f1f-48bcc27c7a72
-- title:
--   Theorem (1.4), p. 16 — Mixing Lemma: ||F(A_0,…,A_d)| − α|A_0|⋯|A_d|/n| ≤ ρ_α(|A_0|⋯|A_d|)^{d/(d+1)}
-- statement:
--   **Theorem (1.4) (Mixing Lemma).** Let $X$ be a $d$-dimensional complex with a complete skeleton on $n$ vertices, $d\ge1$, and fix $\alpha\in\mathbb R$. Let
--   $$\rho_\alpha=\max\bigl\{|\mu|\;\big|\;\mu\in\operatorname{Spec}(\alpha I-\Delta^+)\big|_{Z_{d-1}}\bigr\}=\bigl\|(\alpha I-\Delta^+)\big|_{Z_{d-1}}\bigr\|,$$
--   the largest absolute value of an eigenvalue of $\alpha I-\Delta^+$ on the $(d-1)$-cycles. For any pairwise disjoint sets of vertices $A_0,\dots,A_d$ (not necessarily a partition),
--   $$\left|\,|F(A_0,\dots,A_d)|-\frac{\alpha\cdot|A_0|\cdots|A_d|}{n}\right|\le\rho_\alpha\cdot\bigl(|A_0|\cdots|A_d|\bigr)^{\frac d{d+1}}.$$
--
--   Here $F(A_0,\dots,A_d)$ is the set of $d$-cells with exactly one vertex in each $A_i$. The theorem generalizes the Expander Mixing Lemma of graphs ($d=1$): the number of $d$-cells across $d+1$ disjoint vertex sets is close to its expected value $\alpha\prod|A_i|/n$, with an error controlled by the spectrum of the upper Laplacian.
--
--   **Formalization Note.** $d\ge1$ is added (the Laplacians act on $\Omega^{d-1}$). $\rho_\alpha$ is not defined as a maximum: the statement is made for every $\rho$ with $|\mu|\le\rho$ for all eigenvalues $\mu$ of $\alpha I-\Delta^+$ on $Z_{d-1}$, which is equivalent to the statement for $\rho_\alpha$ (the maximum is such a $\rho$, and any such $\rho$ is at least the maximum); an empty eigenvalue set cannot make it trivially true through a default value. The page's first expression $\max\{|\mu_{\binom{n-1}{d-1}}|,|\mu_m|\}$ for $\rho_\alpha$ relies on Proposition 3.3 and equals the one used, by (4.10). No hypothesis $n\ge d+1$ is needed: if $n\le d$, some $A_i$ is empty and both sides are $0$. The power is `Real.rpow` with exponent $d/(d+1)$ computed in $\mathbb R$.
-- source:
--   Parzanchevski, Rosenthal and Tessler, Isoperimetric inequalities in simplicial complexes, arXiv:1207.0638v3, §4.3, p. 16, Theorem (1.4) (precise form of Theorem 1.4, p. 4)

import Mathlib
import Definitions.Def_SimplicialIso_Mixing_Setting

namespace SimplicialIso.Mixing

open Finset
open scoped InnerProductSpace

/-- Theorem (1.4), p. 16 (the Mixing Lemma, precise form): for a `d`-complex `X` with a complete
skeleton, `α ∈ ℝ`, disjoint vertex sets `A_0, …, A_d` (not necessarily a partition), and any `ρ`
bounding the absolute value of every eigenvalue of `αI − Δ⁺` on `Z_{d-1}` (in particular
`ρ = ρ_α = ‖(αI − Δ⁺)|_{Z_{d-1}}‖`),
`| |F(A_0, …, A_d)| − α |A_0| ⋯ |A_d| / n | ≤ ρ (|A_0| ⋯ |A_d|)^{d/(d+1)}`. -/
theorem theorem_1_4 (n d : ℕ) (hd : 1 ≤ d) (X : Complex n d) (α : ℝ)
    (A : Fin (d + 1) → Finset (Fin n)) (hA : Pairwise (fun i j => Disjoint (A i) (A j))) (ρ : ℝ)
    (hρ : ∀ μ, IsCycleEigenvalue (α • LinearMap.id - upLap X) μ → |μ| ≤ ρ) :
    |((F X A).card : ℝ) - α * (∏ i, ((A i).card : ℝ)) / n| ≤
      ρ * (∏ i, ((A i).card : ℝ)) ^ ((d : ℝ) / (d + 1)) := by sorry

end SimplicialIso.Mixing
