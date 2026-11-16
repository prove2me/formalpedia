-- Prove2me | Theorems.Thm_SelectiveDPT_Supplement_theorem_3_6
-- name    : SelectiveDPT.Supplement.theorem_3_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T00:32:52.891995+00:00
-- url     : https://prove2.me/theorems/8b208a87-76c5-438e-b165-c79808a02747
-- title:
--   Theorem 3.6 — Boolean conversion: $\Gamma = 2I-\Gamma_\pm$ is a multiplicative witness with $\lambda = 19/10$, $\eta = 1/2$, loss $\zeta_2(\varepsilon) < 14$
-- statement:
--   Let $f : D \to \{0,1\}$ be a function, $\mathcal D$ a distribution on $D \subseteq X^n$, and $\varepsilon \in [0, 1/2)$. Let $\Gamma_\pm$ be a witness to the negative-weights adversary method (Proposition 2.5) for $f$ on $\mathcal D$, giving the lower bound
--   $$T_\pm = \frac{1 - 2\sqrt{\varepsilon(1-\varepsilon)}}{2\max_i \|\Gamma_\pm \circ D_i\|}.$$
--   Let $\Gamma = 2I - \Gamma_\pm$, $W^t_{\Gamma_\pm} = \mathrm{Tr}[\Gamma_\pm\rho^t_I]$ and $W^t = \mathrm{Tr}[\Gamma\rho^t_I]$. Then $\Gamma$ is a witness to the multiplicative adversary method (Proposition 2.12) with $\lambda = 19/10$ and $\eta = 1/2$. Moreover:
--   1. $W^0 = W^0_{\Gamma_\pm} = 1$;
--   2. $\ln(W^{t+1}/W^t) \le \max_{i,p,\rho}\ln\big(\mathrm{Tr}[\Gamma O_{i,p}^\dagger\rho O_{i,p}]/\mathrm{Tr}[\Gamma\rho]\big) \le 2\max_i\|\Gamma_\pm \circ D_i\|$;
--   3. $\ln\big(1 + (\lambda-1)(\sqrt{1-\varepsilon} - \sqrt\eta)^2\big) = \ln\big(1 + 9(\sqrt{1-\varepsilon} - 1/\sqrt2)^2/10\big) = (1 - 2\sqrt{\varepsilon(1-\varepsilon)})/\zeta_2(\varepsilon)$ with $\zeta_2(\varepsilon) < 14$.
--
--   Thus $\Gamma$ gives the query lower bound
--   $$T \ge \frac{\ln(1 + 9(\sqrt{1-\varepsilon} - 1/\sqrt2)^2/10)}{\ln(W^{t+1}/W^t)} \ge \frac{1 - 2\sqrt{\varepsilon(1-\varepsilon)}}{2\zeta_2(\varepsilon)\max_i\|\Gamma_\pm\circ D_i\|} \ge \frac{T_\pm}{\zeta_2(\varepsilon)} \ge \frac{T_\pm}{14}$$
--   via the multiplicative adversary method; in particular $\mathrm{MADV}^{\mathcal D}_{\varepsilon,19/10,1/2}(f) \ge T_\pm/14$.
--
--   Compared with the general conversion (Theorem 3.1, $\eta \approx 0.608$), this gives $\eta = 1/2 = 1/|Y|$, which is what the list-decoding theorem (Theorem 5.9) needs.
--
--   Differences from the source:
--   - reading: Γ± a witness … that gives a query lower bound of T± → T± = (1 − 2√(ε(1−ε)))/(2 max_i ‖Γ± ∘ D_i‖); reason: the bound of Proposition 2.5 for Boolean f (τ±(ε) = 2√(ε(1−ε)), p.13); with it the step (1 − 2√(ε(1−ε)))/(2ζ₂M) ≥ T±/ζ₂ is the equality the proof uses
--   - encoding: W^0 = W^0_{Γ±} = 1 and ln(W^{t+1}/W^t) ≤ max_{i,p,ρ} … ≤ 2 max_i ‖Γ± ∘ D_i‖ → ⟨D|Γ|D⟩ = ⟨D|Γ±|D⟩ = 1; the bound for every query (i, p) and density matrix ρ, and for the rate c(Γ) (base rate); reason: ρ⁰_I = |D⟩⟨D| before any query; c(Γ) is the maximum of the ratios (Remark 2.13); the base mission's encoding of Theorem 3.1
--   - encoding: T ≥ ln(…)/ln(W^{t+1}/W^t) ≥ … ≥ T±/14 via that multiplicative adversary method → each step of the chain, with the multiplicative bound log_{c(Γ)}(1 + (λ−1)(√(1−ε) − √η)²), and T±/14 ≤ MADV^D_{ε,19/10,1/2}(f) in [0, ∞]; reason: the base mission's encoding of Theorem 3.1; MADV is the supremum of the multiplicative bounds over witnesses
--   - encoding: f : D → {0,1} → f : (ι → ZMod d) → Bool, read only on D; reason: {0,1} is Bool; values outside D are never read
--   - encoding: D ⊆ X^n → D ⊆ ι → ZMod d for any finite index type ι; reason: X = Z_d (p.9); the index set [n] is any finite type, as in the base mission's Theorem 3.1
-- source:
--   Beame–Kornerup–Whitmeyer, Strong Selective and List-Decoding Direct Product Theorems for Quantum Query Complexity, arXiv:2609.26678, Theorem 3.6, p.24

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_SelectiveDPT_IsNegAdvWitness
import Definitions.Def_SelectiveDPT_maskC
import Definitions.Def_SelectiveDPT_madv
import Definitions.Def_SelectiveDPT_Supplement_zeta2

open Matrix
open scoped ENNReal

namespace SelectiveDPT.Supplement

open QAlgorithms

/-- Theorem 3.6 of arXiv:2609.26678 (Beame–Kornerup–Whitmeyer), p.24: let `f : D → {0,1}` be a
function and `D` a distribution over `D ⊆ X^n`. Suppose `Γ±` is a witness to Proposition 2.5 for
computing `f` on `D` with error `ε ∈ [0, 1/2)` that gives a query lower bound of `T±`. Let
`Γ = 2I − Γ±` and define progress measures `W^t_{Γ±} = Tr[Γ± ρ^t_I]`, `W^t = Tr[Γ ρ^t_I]`. Then
`Γ` is a witness to the multiplicative adversary method with `λ = 19/10`, `η = 1/2`. Moreover
1. `W⁰ = W⁰_{Γ±} = 1`;
2. `ln(W^{t+1}/W^t) ≤ max_{i,p,ρ} ln(Tr[Γ O†_{i,p} ρ O_{i,p}]/Tr[Γρ]) ≤ 2 max_i ‖Γ± ∘ D_i‖`;
3. `ln(1 + (λ−1)(√(1−ε) − √η)²) = ln(1 + 9(√(1−ε) − 1/√2)²/10) = (1 − 2√(ε(1−ε)))/ζ₂(ε)` with
   `ζ₂(ε) < 14`.
Thus `T ≥ ln(1 + 9(√(1−ε) − 1/√2)²/10)/ln(W^{t+1}/W^t) ≥ (1 − 2√(ε(1−ε)))/(2ζ₂(ε) max_i ‖Γ± ∘ D_i‖)
≥ T±/ζ₂(ε) ≥ T±/14`.

Here `T± = (1 − 2√(ε(1−ε)))/(2 max_i ‖Γ± ∘ D_i‖)`, the bound of Proposition 2.5 for Boolean `f`
(`τ±(ε) = 2√(ε(1−ε))`, p.13). As in the base mission's Theorem 3.1, part 1 is stated for
`ρ⁰_I = |D⟩⟨D|`; part 2 for every query `(i, p)` and density matrix `ρ`, and for the rate `c(Γ)`
(base `rate`, the maximum of these ratios by Remark 2.13); the multiplicative lower bound is
`log_{c(Γ)}(1 + (λ−1)(√(1−ε) − √η)²)`, and the last clause bounds `MADV^D_{ε,λ,η}(f)`. `{0,1}` is
`Bool`. -/
theorem theorem_3_6 {ι : Type*} [Fintype ι] [DecidableEq ι] {d : ℕ} [NeZero d]
    (D : Finset (ι → ZMod d)) (μ : (ι → ZMod d) → ℝ) (hμ : IsDistOn μ D)
    (f : (ι → ZMod d) → Bool) (ε : ℝ) (hε₀ : 0 ≤ ε) (hε₁ : ε < 1 / 2) (Γpm : Matrix D D ℂ)
    (hΓ : IsNegAdvWitness μ D f Γpm) :
    let Γ : Matrix D D ℂ := (2 : ℂ) • (1 : Matrix D D ℂ) - Γpm
    let lam : ℝ := 19 / 10
    let η : ℝ := 1 / 2
    let M : ℝ := ⨆ i : ι, specNorm (maskC Γpm i)
    let Tpm : ℝ := (1 - 2 * Real.sqrt (ε * (1 - ε))) / (2 * M)
    let X : ℝ := 1 + (lam - 1) * (Real.sqrt (1 - ε) - Real.sqrt η) ^ 2
    IsMultAdvWitness μ D (fun x y => f x = y) Γ lam η ∧
    (star (sqrtDist μ D) ⬝ᵥ (Γ *ᵥ sqrtDist μ D)).re = 1 ∧
    (star (sqrtDist μ D) ⬝ᵥ (Γpm *ᵥ sqrtDist μ D)).re = 1 ∧
    (∀ (q : ι × ZMod d) (ρ : Matrix D D ℂ), IsDensityMatrix ρ →
      Real.log ((Γ * (oracleOn D q.1 q.2).conjTranspose * ρ * oracleOn D q.1 q.2).trace.re /
        (Γ * ρ).trace.re) ≤ 2 * M) ∧
    Real.log (rate D Γ) ≤ 2 * M ∧
    X = 1 + 9 * (Real.sqrt (1 - ε) - 1 / Real.sqrt 2) ^ 2 / 10 ∧
    Real.log X = (1 - 2 * Real.sqrt (ε * (1 - ε))) / zeta2 ε ∧
    zeta2 ε < 14 ∧
    (1 - 2 * Real.sqrt (ε * (1 - ε))) / (2 * zeta2 ε * M) ≤ Real.logb (rate D Γ) X ∧
    Tpm / zeta2 ε ≤ (1 - 2 * Real.sqrt (ε * (1 - ε))) / (2 * zeta2 ε * M) ∧
    Tpm / 14 ≤ Tpm / zeta2 ε ∧
    ENNReal.ofReal (Tpm / 14) ≤ madv μ D (fun x y => f x = y) ε lam η := by sorry

end SelectiveDPT.Supplement
