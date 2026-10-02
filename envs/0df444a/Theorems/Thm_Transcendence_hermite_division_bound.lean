-- Prove2me | Theorems.Thm_Transcendence_hermite_division_bound
-- name    : Transcendence.hermite_division_bound
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-02T08:18:41.537888+00:00
-- url     : https://prove2.me/theorems/55157768-e9dd-4629-8ed1-e71c85e6e6da
-- title:
--   Hermite division of an entire function at nodes in a disc of radius r, with bounds on the disc of radius R ≥ 5r (Step 2.4 of the proof of Lemma 4.8)
-- statement:
--   Let $0 < r$ and $5r \le R$, let $Z$ be a finite multiset of complex numbers $\zeta$ with $|\zeta| \le r$, put $p = |Z|$ and $P(x) = \prod_{\zeta \in Z}(x - \zeta)$, and let $u$ be an entire function with $|u| \le M$ on the closed disc of radius $R$. Then there are a polynomial $\rho$ of degree less than $p$ and an entire function $q$ with
--
--   $$u(x) = \rho(x) + P(x)\,q(x) \qquad (x \in \mathbb{C}),$$
--
--   such that $\rho^{(k)}(\zeta) = u^{(k)}(\zeta)$ whenever $k$ is less than the multiplicity of $\zeta$ in $Z$, and
--
--   $$2|\rho(x)| + M \le 3^{p}M, \qquad |q(x)| \le (3/R)^{p}M \qquad (|x| \le R).$$
--
--   In one variable, this is the existence part of Lemma 4.8 c) and d) of Waldschmidt's book, with the bounds proved in Step 2.4 of its proof. It is the division step of `Transcendence.coord_hermite_step`.
--
--   It is one step of the proof of Baker's theorem formalised in this mission, which follows Chapter 4 of Waldschmidt's book: Baker's theorem from the criterion of Schneider–Lang for Cartesian products, as observed by Bertrand and Masser (1980).
--
--   **Novelty.** None: $\rho$ and $q$ are the book's $f_0$ and $f_n$, built by the same induction on the nodes (Step 2.4, pp. 125–126). The bound $2|\rho| + M \le 3^pM$ is the form that this induction carries; it is slightly sharper than the book's $|f_0|_R \le 3^p|f|_R$. The contribution of this node is the formal proof.
-- source:
--   M. Waldschmidt, Diophantine Approximation on Linear Algebraic Groups, Grundlehren 326, Springer, 2000, Lemma 4.8 c)–d) (p. 123) in one variable, with the bounds of Step 2.4 of its proof (pp. 125–126). Formal proof: Diaz modulus mission, 2 October 2026 (C. Perassi).

import Mathlib

open Polynomial

namespace Transcendence

/-- **Hermite division with bounds** (Waldschmidt, *Diophantine Approximation on Linear Algebraic Groups*,
proof of Prop. 4.7, Step 2.4). Let `u` be an entire function with `|u| ≤ M` on the closed disc of radius `R`,
and let `Z` be a multiset of nodes in the closed disc of radius `r > 0`, where `R ≥ 5r`. Then `u = ρ + P·q`
with `P(x) = ∏_{ζ ∈ Z} (x - ζ)`, where `ρ` is a polynomial of degree `< |Z|` whose derivatives of order `< m`
at a node of multiplicity `m` are those of `u`, and `q` is entire; on the closed disc of radius `R`,
`2|ρ| + M ≤ 3^|Z|·M` and `|q| ≤ (3/R)^|Z|·M`. -/
theorem hermite_division_bound {r R : ℝ} (hr : 0 < r) (hR : 5 * r ≤ R) (Z : Multiset ℂ)
    (hZ : ∀ ζ ∈ Z, ‖ζ‖ ≤ r) {u : ℂ → ℂ} (hu : Differentiable ℂ u) {M : ℝ}
    (hM : ∀ w ∈ Metric.closedBall (0 : ℂ) R, ‖u w‖ ≤ M) :
    ∃ (ρ : ℂ[X]) (q : ℂ → ℂ), ρ ∈ degreeLT ℂ (Multiset.card Z) ∧ Differentiable ℂ q ∧
      (∀ x, u x = ρ.eval x + (Z.map fun ζ => x - ζ).prod * q x) ∧
      (∀ ζ, ∀ k < Z.count ζ, (derivative^[k] ρ).eval ζ = iteratedDeriv k u ζ) ∧
      ∀ x ∈ Metric.closedBall (0 : ℂ) R,
        2 * ‖ρ.eval x‖ + M ≤ 3 ^ Multiset.card Z * M ∧ ‖q x‖ ≤ (3 / R) ^ Multiset.card Z * M := by
  sorry

end Transcendence
