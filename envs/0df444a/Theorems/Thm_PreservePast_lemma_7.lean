-- Prove2me | Theorems.Thm_PreservePast_lemma_7
-- name    : PreservePast.lemma_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T10:39:58.390887+00:00
-- url     : https://prove2.me/theorems/cb4cf161-567d-4513-96d4-faddb0199c32
-- title:
--   Lemma 7 — same-rank norm duality
-- statement:
--   Let $C_0\succ0$ be an $n\times n$ positive definite matrix, $G\in\mathbb R^{m\times n}$, $R>1$, $x\in\mathbb R^n$ and $p\in\mathbb R^m$ unit vectors, $1\le r\le\min\{m,n\}$, and let $Q\subseteq\mathbb R^m$ be a subspace containing $p$ ($Q=\mathbb R^m$ is the unconstrained case). Put
--   $$
--   g(H)=\langle G,H\rangle+\tfrac12\operatorname{tr}(HC_0H^\top),\qquad \mathcal F=\{H:\ Hx=p,\ \operatorname{rank}H\le r,\ \operatorname{range}H\subseteq Q\}.
--   $$
--   Then
--   $$
--   \min_{H\in\mathcal F,\ \|H\|_F\le R}g(H)=\max_{z\ge0}\ \min_{H\in\mathcal F}\Big[g(H)+\frac z2\big(\|H\|_F^2-R^2\big)\Big],
--   $$
--   and both extrema are attained, as is the inner minimum for every $z\ge0$.
--
--   Same-rank duality lets the upper bound compare the full and the restricted output spaces uniformly over the norm multiplier $z$, although the rank constraint is not convex.
--
--   **Formalization Note** The equality and the attainment are stated as four clauses: a primal minimizer $H_0$ exists; for every $z\ge0$ the penalized objective has a minimizer over $\mathcal F$; at some $z_*\ge0$ that minimum equals $g(H_0)$; for every $z\ge0$ that minimum is at most $g(H_0)$.
--
--   Differences from the source:
--   - encoding: (48) for 𝓕_r, and 'the same equality holds' with range in a fixed subspace Q ∋ p → one statement for an arbitrary subspace Q ∋ p; reason: Q = ℝᵐ is the unconstrained case, so the two claims are the two instances
--   - encoding: min = max, both extrema attained → existence of the primal minimizer, of inner minimizers, of an optimal multiplier, and weak duality; reason: the same content written without sInf/sSup
-- source:
--   P. Xu, Information Required to Preserve Past Learning, STOC 2027 submission (held version, PDF sha256 48013ceb…d00fa), §C.3, p.19 (PDF p.21), Lemma 7, (48)

import Mathlib
import Definitions.Def_LowRankMEG_frobNorm
import Definitions.Def_WainwrightHDS_NucNorm_traceInner

open Matrix

namespace PreservePast

/-- **Lemma 7 (same-rank norm duality).** P. Xu, *Information Required to Preserve Past Learning*, STOC 2027 submission (held version,
PDF sha256 48013ceb…d00fa), §C.3, p.19 (PDF p.21): "Let C₀ ≻ 0,
G ∈ ℝ^{m×n}, R > 1, and let x, p be unit vectors. Put g(H) = ⟨G, H⟩ + ½ tr(HC₀H^⊤),
𝓕_r = {H : Hx = p, rank H ≤ r}, where 1 ≤ r ≤ min{m, n}. Then
min_{H∈𝓕_r, ‖H‖_F≤R} g(H) = max_{z≥0} min_{H∈𝓕_r} [g(H) + (z/2)(‖H‖²_F − R²)]. (48)
Both extrema are attained. The same equality holds when every matrix is also required to have range
in a fixed subspace Q containing p."

Stated for an arbitrary subspace `Q ∋ p` (`Q = ℝᵐ` is the unconstrained case): with
`𝓕 = {H : Hx = p, rank H ≤ r, range H ⊆ Q}` and `φ_z(H) = g(H) + (z/2)(‖H‖²_F − R²)`,
(a) `g` attains its minimum on `𝓕 ∩ {‖H‖_F ≤ R}` at some `H₀`; (b) for every `z ≥ 0`, `φ_z`
attains its minimum on `𝓕`; (c) at some `z* ≥ 0` the minimum of `φ_{z*}` over `𝓕` equals
`g(H₀)`; (d) for every `z ≥ 0` the minimum of `φ_z` over `𝓕` is at most `g(H₀)`.

**Formalization Note.** (a)–(d) together say that both sides of (48) are attained and equal.
`range H` is the range of `v ↦ Hv`; unit vectors are `Σ xᵢ² = 1`, `Σ pⱼ² = 1`. -/
theorem lemma_7 {m n r : ℕ} (C₀ : Matrix (Fin n) (Fin n) ℝ) (hC₀ : C₀.PosDef)
    (G : Matrix (Fin m) (Fin n) ℝ) (R : ℝ) (hR : 1 < R) (x : Fin n → ℝ) (p : Fin m → ℝ)
    (hx : ∑ i, x i ^ 2 = 1) (hp : ∑ j, p j ^ 2 = 1) (hr1 : 1 ≤ r) (hr : r ≤ min m n)
    (Q : Submodule ℝ (Fin m → ℝ)) (hpQ : p ∈ Q) :
    let g : Matrix (Fin m) (Fin n) ℝ → ℝ := fun H =>
      WainwrightHDS.NucNorm.traceInner G H + (1 / 2) * (H * C₀ * H.transpose).trace
    let F : Set (Matrix (Fin m) (Fin n) ℝ) :=
      {H | H *ᵥ x = p ∧ H.rank ≤ r ∧ LinearMap.range (Matrix.toLin' H) ≤ Q}
    let φ : ℝ → Matrix (Fin m) (Fin n) ℝ → ℝ := fun z H =>
      g H + z / 2 * (LowRankMEG.frobNorm H ^ 2 - R ^ 2)
    ∃ H₀ ∈ F, LowRankMEG.frobNorm H₀ ≤ R ∧ (∀ H ∈ F, LowRankMEG.frobNorm H ≤ R → g H₀ ≤ g H) ∧
      (∀ z : ℝ, 0 ≤ z → ∃ Hz ∈ F, ∀ H ∈ F, φ z Hz ≤ φ z H) ∧
      (∃ zs : ℝ, 0 ≤ zs ∧ ∃ Hs ∈ F, (∀ H ∈ F, φ zs Hs ≤ φ zs H) ∧ φ zs Hs = g H₀) ∧
      (∀ z : ℝ, 0 ≤ z → ∀ Hz ∈ F, (∀ H ∈ F, φ z Hz ≤ φ z H) → φ z Hz ≤ g H₀) := by sorry

end PreservePast
