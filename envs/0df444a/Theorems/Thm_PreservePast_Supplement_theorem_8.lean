-- Prove2me | Theorems.Thm_PreservePast_Supplement_theorem_8
-- name    : PreservePast.Supplement.theorem_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-22T04:35:47.499462+00:00
-- url     : https://prove2.me/theorems/ae515655-bcaa-466f-aa61-051f0954d844
-- title:
--   Theorem 8 — uniform BSC capacity window
-- statement:
--   In the nearest-of-$k$ experiment on the cube, fix $\rho_0<1$ and $T_0<\infty$. Let $k\to\infty$, allow $0<\rho\le\rho_0$, and set
--   $$\ell=\ln k,\qquad D=dF(\rho),\qquad V=d(1-\rho^2)\theta^2,\qquad z=\frac{D-\ell}{\sqrt V},\qquad |z|\le T_0,$$
--   with $\theta=\operatorname{atanh}\rho$. Put $u=\Phi(z)$ and $\omega_\ell=(\ln\ell)^{3/2}/\sqrt\ell$. Uniformly over these parameters,
--   $$S^\ast=u+O_{\rho_0,T_0}\Big(\frac{\ln\ell}{\sqrt\ell}\Big),$$
--   $$\frac{I_{\min}(S)}{kd}=\frac Su+O_{\rho_0,T_0}(\omega_\ell),\qquad 0\le S\le S^\ast,$$
--   uniformly over all feasible target successes, and the same law holds for fixed width:
--   $$\frac{B_{\min}(S)}{kd}=\frac S{\Phi(z)}+O_{\rho_0,T_0}(\omega_\ell),$$
--   with upper remainder $O_{\rho_0,T_0}(\ln\ell/\sqrt\ell)$, also at exact finite-model Bayes success $S=S^\ast$.
--
--   At leading order a retained record costs $d$ bits and contributes at most $u$ conditional success, so an $S/u$ fraction of the records is optimal.
--
--   **Formalization Note** $I_{\min}(S)$ and $B_{\min}(S)$ are the least information $I(X;M\mid R)$ and the least register width among protocols of success at least $S$.
--
--   Differences from the source:
--   - encoding: O_{ρ₀,T₀}(·) uniformly as k → ∞ → a constant C > 0 and a threshold k₀ chosen after ρ₀, T₀ and before k, d, ρ and the target S; reason: spells out the uniform O; S may depend on the parameters
--   - encoding: I_min(S)/(kd) = S/u + O(ω_ℓ) and B_min(S)/(kd) = S/Φ(z) + O(ω_ℓ) with upper remainder O(ln ℓ/√ℓ) → every protocol of success ≥ S has information (resp. width) ≥ (S/u − Cω_ℓ)kd, and some protocol of success ≥ S has information ≤ (S/u + Cω_ℓ)kd (resp. width ≤ (S/u + C ln ℓ/√ℓ)kd); reason: two-part form of a least cost; avoids junk values of infima
--   - encoding: S* is the optimal success when the decoder also has the full X → the closed form 𝔼_X Σ_z max_j P_{X_j}(z)/k; reason: the maximum-a-posteriori rule attains the optimum
-- source:
--   P. Xu, Information Required to Preserve Past Learning, STOC 2027 submission (held version, PDF sha256 48013ceb55cb5da782f256c3a4d1c95195bee48a2f4d0b2ed1e22bccd96d00fa), Theorem 8, p.11 (PDF p.13), eqs. (23)–(26); Definition 1, p.10 (PDF p.12)

import Mathlib
import Definitions.Def_PreservePast_Supplement_IdProtocol

open MeasureTheory

namespace PreservePast.Supplement

/-- **Theorem 8 (Uniform BSC capacity window).** P. Xu, *Information Required to Preserve Past Learning*, STOC 2027 submission (held version,
PDF sha256 48013ceb…d00fa), Theorem 8, p.11 (PDF p.13),
eqs. (23)–(26); the experiment is Definition 1, p.10 (PDF p.12).

Fix `ρ₀ < 1` and `T₀ < ∞`. As `k → ∞`, uniformly over `d` and `0 < ρ ≤ ρ₀` with `|z| ≤ T₀`,
where `ℓ = ln k`, `z = (dF(ρ) − ℓ)/√(d(1−ρ²)θ²)`, `u = Φ(z)`, `ω_ℓ = (ln ℓ)^{3/2}/√ℓ`:
(24) `S* = u + O(ln ℓ/√ℓ)`; (25) `I_min(S)/(kd) = S/u + O(ω_ℓ)` for `0 ≤ S ≤ S*`;
(26) `B_min(S)/(kd) = S/Φ(z) + O(ω_ℓ)`, with upper remainder `O(ln ℓ/√ℓ)`, also at `S = S*`.

**Formalization Note.** `O_{ρ₀,T₀}(·)` uniformly as `k → ∞` is a constant `C` and a threshold
`k₀` chosen after `ρ₀, T₀` and before `k, d, ρ, S` (so `S` may depend on the parameters).
The least costs are stated in two parts: for `I_min`, every protocol of success `≥ S` has
`I(X; M | R) ≥ (S/u − Cω_ℓ)kd` bits and some protocol of success `≥ S` has
`I(X; M | R) ≤ (S/u + Cω_ℓ)kd`; for `B_min`, every protocol of success `≥ S` whose message
fits `B` bits has `B ≥ (S/u − Cω_ℓ)kd` and some such protocol has
`B ≤ (S/u + C ln ℓ/√ℓ)kd` (the sharper upper remainder of the source). Information is an
extended nonnegative real, compared through `ENNReal.ofReal`. -/
theorem theorem_8 :
    ∀ ρ₀ T₀ : ℝ, 0 < ρ₀ → ρ₀ < 1 → 0 ≤ T₀ → ∃ (C : ℝ) (k₀ : ℕ), 0 < C ∧ 2 ≤ k₀ ∧
      ∀ (k d : ℕ) (ρ : ℝ), k₀ ≤ k → 1 ≤ d → 0 < ρ → ρ ≤ ρ₀ → |bscZ k d ρ| ≤ T₀ →
        |bayesSuccess k d ρ - stdNormalCdf (bscZ k d ρ)| ≤
            C * (Real.log (Real.log k) / Real.sqrt (Real.log k)) ∧
        ∀ S : ℝ, 0 ≤ S → S ≤ bayesSuccess k d ρ →
          (∀ π : IdProtocol k d, S ≤ π.success ρ →
            ENNReal.ofReal ((S / stdNormalCdf (bscZ k d ρ) -
              C * (Real.log (Real.log k) ^ ((3 : ℝ) / 2) / Real.sqrt (Real.log k))) * (k * d)) ≤
              π.info) ∧
          (∃ π : IdProtocol k d, S ≤ π.success ρ ∧
            π.info ≤ ENNReal.ofReal ((S / stdNormalCdf (bscZ k d ρ) +
              C * (Real.log (Real.log k) ^ ((3 : ℝ) / 2) / Real.sqrt (Real.log k))) * (k * d))) ∧
          (∀ (π : IdProtocol k d) (B : ℕ), π.HasWidth B → S ≤ π.success ρ →
            (S / stdNormalCdf (bscZ k d ρ) -
              C * (Real.log (Real.log k) ^ ((3 : ℝ) / 2) / Real.sqrt (Real.log k))) * (k * d) ≤
              (B : ℝ)) ∧
          ∃ (π : IdProtocol k d) (B : ℕ), π.HasWidth B ∧ S ≤ π.success ρ ∧
            (B : ℝ) ≤ (S / stdNormalCdf (bscZ k d ρ) +
              C * (Real.log (Real.log k) / Real.sqrt (Real.log k))) * (k * d) := by sorry

end PreservePast.Supplement
