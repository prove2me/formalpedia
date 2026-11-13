-- Prove2me | Theorems.Thm_PhaseEncodedQGE_eq_2_beta_zero
-- name    : PhaseEncodedQGE.eq_2_beta_zero
-- status  : Open
-- author  : @iris
-- created : 2026-11-12T06:50:24.509434+00:00
-- url     : https://prove2.me/theorems/6d02252c-8c2a-42cb-bae8-e63771c36388
-- title:
--   Eq. (2) — at $\beta=0$, $\mu(x)=c^{2\ell}s^{2(n-\ell)}$ with layer ratio $t^{-2}$; Hadamard $\mu=2^{-n}$
-- statement:
--   Let $G$ be a cubic graph on $n$ vertices with the degree-aware preparation (every vertex receives $R_X(\eta)$), and put $c=\cos(\eta/2)$, $s=\sin(\eta/2)$, $t=\tan(\eta/2)$. For an outcome $x$ with $\ell=|D(x)|$ defects,
--
--   1. at $\beta=0$, for every mixer axis and every number of repetitions,
--   $$p_G(x;0)=\mu(x)=c^{2\ell}s^{2(n-\ell)},$$
--   independently of $G$;
--   2. if $c\ne0\ne s$, consecutive layer weights satisfy $\mu_{\ell+1}/\mu_\ell=t^{-2}$ for $0\le\ell<n$;
--   3. at $\eta=23/8$, $t^{-2}=0.0180$ to the printed four decimals;
--   4. under the Hadamard preparation $\mu(x)=2^{-n}$ for every $x$.
--
--   This is the zeroth-order picture on which the layer structure rests: when $t>1$ the Born distribution at $\beta=0$ is constant on each defect layer and strictly decreasing in the defect count, so the sorted readout lists the outcomes by defect count.
--
--   Differences from the source:
--   - generalization: the degree-prepared members and the standing assumption $0<\eta<\pi$, $t>1$ of the paragraph → every mixer axis $P$, every $r$, every $\eta$ (the ratio for $\cos(\eta/2)\ne0\ne\sin(\eta/2)$ and $\ell<n$); the Hadamard clause for every $P$ and $r$; reason: at β = 0 the mixer is the identity and the edge phase has modulus one, so the formula holds at every angle and for every member; it specializes to the paper's members and angles
--   - encoding: $t^{-2}=0.0180$ → $|\tan(23/16)^{-2}-0.0180|<5\cdot10^{-5}$; reason: a printed four-decimal value is a bound at half a unit of its last digit
-- source:
--   Miller, Lee, Structural Accessibility in Phase-Encoded Quantum Graph Embeddings, STOC 2027 submission (build 2026-11-03, sha256 f1132658…7c51), §2, p.5 (PDF p.6), eq. (2) and the last sentence of 'Defect layers and blocks'

import Mathlib
import Definitions.Def_PhaseEncodedQGE_Circuit
set_option autoImplicit false

namespace PhaseEncodedQGE

open Matrix

/-- The `β = 0` distribution (Miller, Lee, *Structural Accessibility in Phase-Encoded Quantum Graph Embeddings*, STOC 2027 submission (build 2026-11-03), §2, p.5, eq. (2), and the sentence after it).

Degree-aware preparation on a cubic graph: at `β = 0`,
`p_G(x; 0) = µ(x) = c^{2ℓ} s^{2(n−ℓ)}` with `c = cos(η/2)`, `s = sin(η/2)` and `ℓ = |D(x)|`,
independently of `G`; consecutive layer weights have ratio `µ_{ℓ+1}/µ_ℓ = t^{−2}`, which is `0.0180`
at `η = 23/8`. The Hadamard preparation has no layers: `µ(x) = 2^{−n}` for every `x`.

**Formalization Note** `ℓ` is `(defects x).card`. The formula is stated for every mixer axis `P`
and every number `r` of repetitions (at `β = 0` the mixer is the identity) and for every angle `η`;
the ratio needs `c ≠ 0 ≠ s` and is stated for `0 ≤ ℓ < n`. The printed `0.0180` is a 4-decimal
value, stated as a bound at that precision. `2^{−n}` is `(2⁻¹)^n`. -/
theorem eq_2_beta_zero :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)), IsCubic G → ∀ (P : Axis) (r : ℕ) (η γ : ℝ)
      (x : Outcome n),
        born (degPrep G η) P r G γ 0 x =
          Real.cos (η / 2) ^ (2 * (defects x).card) *
            Real.sin (η / 2) ^ (2 * (n - (defects x).card))) ∧
    (∀ (n ℓ : ℕ) (η : ℝ), Real.cos (η / 2) ≠ 0 → Real.sin (η / 2) ≠ 0 → ℓ < n →
      (Real.cos (η / 2) ^ (2 * (ℓ + 1)) * Real.sin (η / 2) ^ (2 * (n - (ℓ + 1)))) /
          (Real.cos (η / 2) ^ (2 * ℓ) * Real.sin (η / 2) ^ (2 * (n - ℓ))) =
        Real.tan (η / 2) ^ (-2 : ℤ)) ∧
    |Real.tan ((23 / 8 : ℝ) / 2) ^ (-2 : ℤ) - 0.0180| < 5e-5 ∧
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)), IsCubic G → ∀ (P : Axis) (r : ℕ) (γ : ℝ)
      (x : Outcome n), born (hadPrep n) P r G γ 0 x = (2 : ℝ)⁻¹ ^ n) := by sorry

end PhaseEncodedQGE
