-- Prove2me | Theorems.Thm_PreservePast_lemma_8
-- name    : PreservePast.lemma_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T10:40:40.802007+00:00
-- url     : https://prove2.me/theorems/b143d9ef-885d-494f-8849-d4d709532726
-- title:
--   Lemma 8 — one subspace for a fixed tail and all positive low-rank perturbations
-- statement:
--   Let $A_0\succeq0$ be an $m\times m$ matrix with $\|A_0\|_{\mathrm{op}}\le M_0$, let $S\subseteq\mathbb R^m$ be a subspace of dimension $s$, and fix $1\le L<m$ and $0<\delta\le\min\{1,M_0\}$. Put
--   $$
--   \eta=\frac\delta{4L},\qquad b_0=\lceil\log_2\max\{1,M_0/\eta\}\rceil,\qquad q=\max\Big\{1,\Big\lceil\tfrac12\log_3\frac{4\max\{M_0+\eta,1\}L}{\delta}\Big\rceil\Big\}.
--   $$
--   Then there is a subspace $U\subseteq\mathbb R^m$, depending only on $A_0,S,L,\delta,M_0$, with
--   $$
--   \dim U\le\min\{m,\ L+s(1+qb_0)\},
--   $$
--   such that every $T\succeq0$ with $\operatorname{range}T\subseteq S$ and $\|A_0+T\|_{\mathrm{op}}\le M_0$ satisfies
--   $$
--   \mathcal K_L(A_0+T)-\mathcal K_L\big((A_0+T)|_U\big)\le\delta .
--   $$
--
--   A single retained space thus captures the top-$L$ trace of every positive perturbation supported on $S$, through all eigenvalue crossings at the cutoff; this is what makes the retained output space of the upper bound independent of the norm multiplier.
--
--   **Formalization Note** "Depending only on" is the quantifier order: $U$ is chosen before $T$. $\|\cdot\|_{\mathrm{op}}$ is the $\ell_2$ operator norm; $\mathcal K_L$ is defined by Ky Fan's maximum principle.
--
--   Differences from the source:
--   - encoding: 𝒦_L(A) = sum of the L largest eigenvalues (of the compression to U) → maximum of Σ_j y_jᵀAy_j over orthonormal L-families (in U); reason: Ky Fan's maximum principle; equal for symmetric A and L ≤ dim U
-- source:
--   P. Xu, Information Required to Preserve Past Learning, STOC 2027 submission (held version, PDF sha256 48013ceb…d00fa), §C.4, p.21 (PDF p.23), Lemma 8, (52)–(54)

import Mathlib
import Definitions.Def_PreservePast_kyFanOn
import Definitions.Def_WainwrightHDS_NucNorm_opNorm2

open Matrix

namespace PreservePast

/-- **Lemma 8 (fixed tail and positive low-rank perturbations).** P. Xu, *Information Required to Preserve Past Learning*, STOC 2027 submission (held version,
PDF sha256 48013ceb…d00fa), §C.4, p.21 (PDF p.23):
"Let A₀ ⪰ 0 act on ℝᵐ, with ‖A₀‖_op ≤ M₀, and let S be an s-dimensional subspace. Fix 1 ≤ L < m
and 0 < δ ≤ min{1, M₀}. Put η = δ/(4L), b₀ = ⌈log₂ max{1, M₀/η}⌉,
q = max{1, ⌈½ log₃ (4 max{M₀ + η, 1}L/δ)⌉}. (52) … There is a subspace U, depending only on
A₀, S, L, δ, M₀, with dim U ≤ min{m, L + s(1 + qb₀)}, (53) such that every T ⪰ 0 satisfying
range T ⊆ S and ‖A₀ + T‖_op ≤ M₀ obeys 𝒦_L(A₀ + T) − 𝒦_L((A₀ + T)|_U) ≤ δ. (54)"

**Formalization Note.** "Depending only on A₀, S, L, δ, M₀" is the quantifier order `∃ U, ∀ T`.
`⪰ 0` is `PosSemidef` (symmetric, positive semidefinite); `‖·‖_op` is the ℓ₂ operator norm;
`𝒦_L(A|_U)` is `kyFanOn L A U` and `𝒦_L(A) = kyFanOn L A ⊤`; `⌈·⌉` is `Nat.ceil` (both arguments
are nonnegative here). -/
theorem lemma_8 {m s L : ℕ} (A₀ : Matrix (Fin m) (Fin m) ℝ) (hA₀ : A₀.PosSemidef) (M₀ : ℝ)
    (hM₀ : WainwrightHDS.NucNorm.opNorm2 A₀ ≤ M₀) (S : Submodule ℝ (Fin m → ℝ))
    (hS : Module.finrank ℝ S = s) (hL1 : 1 ≤ L) (hLm : L < m) (δ : ℝ) (hδ : 0 < δ)
    (hδ1 : δ ≤ min 1 M₀) :
    let η : ℝ := δ / (4 * L)
    let b₀ : ℕ := ⌈Real.logb 2 (max 1 (M₀ / η))⌉₊
    let q : ℕ := max 1 ⌈(1 / 2) * Real.logb 3 (4 * max (M₀ + η) 1 * L / δ)⌉₊
    ∃ U : Submodule ℝ (Fin m → ℝ), Module.finrank ℝ U ≤ min m (L + s * (1 + q * b₀)) ∧
      ∀ T : Matrix (Fin m) (Fin m) ℝ, T.PosSemidef → LinearMap.range (Matrix.toLin' T) ≤ S →
        WainwrightHDS.NucNorm.opNorm2 (A₀ + T) ≤ M₀ →
        kyFanOn L (A₀ + T) ⊤ - kyFanOn L (A₀ + T) U ≤ δ := by sorry

end PreservePast
