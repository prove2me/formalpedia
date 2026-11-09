-- Prove2me | Theorems.Thm_SelectiveDPT_theorem_3_1
-- name    : SelectiveDPT.theorem_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T12:54:27.936296+00:00
-- url     : https://prove2.me/theorems/61c29dde-84a7-41e3-972f-5ea8551a2ddc
-- title:
--   Theorem 3.1 (corrected: last step clamped at 0) — converting a negative-weights witness into a multiplicative one
-- statement:
--   Let $f : D \to Y$, let $\mu$ be a distribution on $D$, let $0 \le \varepsilon \le 1/3$ and let $\Gamma^\pm$ be a witness to Proposition 2.5 for computing $f$ under $\mu$. Write $M = \max_i \|\Gamma^\pm \circ D_i\|$, $T^\pm = (1-\tau^\pm(\varepsilon))/(2M)$ (the lower bound of Proposition 2.5) and
--   $$\Gamma = 2I - \Gamma^\pm,\qquad \lambda = 3 - \Big(\frac{4}{1-\varepsilon}\Big)^{1/3},\qquad \eta = \Big(\frac{1-\varepsilon}{4}\Big)^{1/3},\qquad X = 1 + (\lambda-1)\big(\sqrt{1-\varepsilon}-\sqrt\eta\big)^2 .$$
--   Then:
--
--   1. $(\Gamma, \lambda, \eta)$ is a valid witness for the relational multiplicative adversary bound for $f$ under $\mu$;
--   2. (part 1) $W^0 = \langle\mathcal D|\Gamma|\mathcal D\rangle = 1$;
--   3. (part 2) for every query $(i,p)$ and density matrix $\rho$, $\ln\big(\mathrm{Tr}[\Gamma O_{i,p}^\dagger\rho O_{i,p}]/\mathrm{Tr}[\Gamma\rho]\big) \le 2M$, and $\ln c(\Gamma) \le 2M$;
--   4. (part 3) $\ln X = (1-2\sqrt{\varepsilon(1-\varepsilon)})/\zeta(\varepsilon)$ and $\zeta(\varepsilon) < 58$;
--   5. the multiplicative lower bound satisfies
--   $$\log_{c(\Gamma)} X \;\ge\; \frac{1-2\sqrt{\varepsilon(1-\varepsilon)}}{2\zeta(\varepsilon) M} \;\ge\; \frac{T^\pm}{\zeta(\varepsilon)},$$
--   and, as bounds in $[0,\infty]$, $\max(T^\pm/\zeta(\varepsilon), 0) \ge \max(T^\pm/58, 0)$ and $\mathrm{MADV}^{\mathcal D}_{\varepsilon,\lambda,\eta}(f) \ge \max(T^\pm/58, 0)$.
--
--   So the relational multiplicative adversary loses at most a factor $\zeta(\varepsilon) < 58$ against the negative-weights adversary.
--
--   Differences from the source:
--   - correction: T±/ζ(ε) ≥ T±/58 → the step and the final bound stated in [0, ∞] (ENNReal.ofReal), i.e. max(T±/ζ(ε), 0) ≥ max(T±/58, 0) and MADV ≥ max(T±/58, 0); reason: for ε = 1/3, τ±(1/3) = 2√2/3 + 1/3 ≈ 1.28 > 1, so T± < 0 for every witness (one exists: Γ± = [[0,1],[1,0]] for f(x) = x_1 on Z_2^1 under the uniform distribution) while 0 < ζ(1/3) ≈ 56.1 < 58, hence T±/ζ(1/3) < T±/58; as query lower bounds the values are clamped at 0
--   - reading: part 1: W⁰ = 2 − Tr[Γ±ρ⁰_I] = 1 → ⟨D|Γ|D⟩ = 1; reason: ρ⁰_I = |D⟩⟨D| because the start state does not depend on the input
--   - reading: part 2: ln(W^{t+1}/W^t) ≤ max_{i,p,ρ} ln(Tr[ΓO†ρO]/Tr[Γρ]) ≤ 2 max_i‖Γ±∘D_i‖ → the bound for every (i, p) and density ρ, and ln c(Γ) ≤ 2 max_i‖Γ±∘D_i‖; reason: the first inequality, about an algorithm's progress, is part 2 of Proposition 2.12; the conversion statement is the bound on the maximum, of which c(Γ) is the norm form (Remark 2.13)
--   - reading: Γ gives a query lower bound T ≥ ln(1 + (λ−1)(√(1−ε)−√η)²)/ln(W^{t+1}/W^t) ≥ … → log_{c(Γ)}(1 + (λ−1)(√(1−ε)−√η)²) ≥ … and MADV^D_{ε,λ,η}(f) ≥ …; reason: the lower bound obtained from Γ via Proposition 2.14 is log_c(…), and MADV is its supremum (Definition 2.15)
--   - reading: a witness that gives a query lower bound of T± → T± = (1 − τ±(ε))/(2 max_i‖Γ±∘D_i‖), the general bound of Proposition 2.5; reason: for Boolean Y the tightened bound of Proposition 2.5 is (1 − 2√(ε(1−ε)))/(2M), which the middle term of the chain also bounds
-- source:
--   Beame–Kornerup–Whitmeyer, Strong Selective and List-Decoding Direct Product Theorems for Quantum Query Complexity, arXiv:2609.26678, Theorem 3.1, pp.17–18; proof pp.20–22

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_SelectiveDPT_advPm
import Definitions.Def_SelectiveDPT_madv
import Definitions.Def_SelectiveDPT_zeta

open Matrix
open scoped ENNReal

namespace SelectiveDPT

open QAlgorithms

/-- Theorem 3.1 of arXiv:2609.26678 (Beame–Kornerup–Whitmeyer), pp.17–18: let `f : D → Y` be a
function and `D` a distribution over `D ⊆ X^n`. Suppose `Γ±` is a witness to Proposition 2.5 for
computing `f` on `D` with error `ε ∈ [0, 1/3]` that gives a query lower bound of `T±`. Let
`Γ = 2I − Γ±`. Then `Γ` is a witness to the multiplicative adversary method with
`λ = 3 − (4/(1−ε))^{1/3}`, `η = ((1−ε)/4)^{1/3}`. Moreover
1. `W⁰ = 2 − Tr[Γ± ρ⁰_I] = 1`;
2. `ln(W^{t+1}/W^t) ≤ max_{i,p,ρ} ln(Tr[Γ O†_{i,p} ρ O_{i,p}] / Tr[Γρ]) ≤ 2 max_i ‖Γ± ∘ D_i‖`;
3. `ln(1 + (λ−1)(√(1−ε) − √η)²) = (1 − 2√(ε(1−ε)))/ζ(ε)` with `ζ(ε) < 58`.
Thus `Γ` gives a query lower bound
`T ≥ ln(1 + (λ−1)(√(1−ε) − √η)²)/ln(W^{t+1}/W^t) ≥ (1 − 2√(ε(1−ε)))/(2ζ(ε) max_i ‖Γ± ∘ D_i‖)
 ≥ T±/ζ(ε) ≥ T±/58`.

Here `T± = (1 − τ±(ε)) / (2 max_i ‖Γ± ∘ D_i‖)`. Part 1 is stated for `ρ⁰_I = |D⟩⟨D|` (the input
state before any query); part 2 for every query `(i, p)` and density matrix `ρ`, and for the rate
`c(Γ)`, which is the maximum of these ratios (Remark 2.13); the multiplicative lower bound is
`log_{c(Γ)}(1 + (λ−1)(√(1−ε) − √η)²)`, and the last clause bounds `MADV^D_{ε,λ,η}(f)`.

**Formalization Note (correction).** The printed last step `T±/ζ(ε) ≥ T±/58` needs `T± ≥ 0`; for
`ε` close to `1/3`, `τ±(ε) > 1` (`τ±(1/3) = 2√2/3 + 1/3 ≈ 1.28`) and `T± < 0`, where the real
inequality reverses. As query lower bounds these values are clamped at `0`: the step and the final
bound are stated in `[0, ∞]` via `ENNReal.ofReal`. -/
theorem theorem_3_1 {ι Y : Type*} [Fintype ι] [DecidableEq ι] {d : ℕ} [NeZero d]
    (D : Finset (ι → ZMod d)) (μ : (ι → ZMod d) → ℝ) (hμ : IsDistOn μ D)
    (f : (ι → ZMod d) → Y) (ε : ℝ) (hε₀ : 0 ≤ ε) (hε₁ : ε ≤ 1 / 3) (Γpm : Matrix D D ℂ)
    (hΓ : IsNegAdvWitness μ D f Γpm) :
    let Γ : Matrix D D ℂ := (2 : ℂ) • (1 : Matrix D D ℂ) - Γpm
    let lam : ℝ := 3 - (4 / (1 - ε)) ^ ((1 : ℝ) / 3)
    let η : ℝ := ((1 - ε) / 4) ^ ((1 : ℝ) / 3)
    let M : ℝ := ⨆ i : ι, specNorm (maskC Γpm i)
    let Tpm : ℝ := (1 - tauPm ε) / (2 * M)
    let X : ℝ := 1 + (lam - 1) * (Real.sqrt (1 - ε) - Real.sqrt η) ^ 2
    IsMultAdvWitness μ D (fun x y => f x = y) Γ lam η ∧
    (star (sqrtDist μ D) ⬝ᵥ (Γ *ᵥ sqrtDist μ D)).re = 1 ∧
    (∀ (q : ι × ZMod d) (ρ : Matrix D D ℂ), IsDensityMatrix ρ →
      Real.log ((Γ * (oracleOn D q.1 q.2).conjTranspose * ρ * oracleOn D q.1 q.2).trace.re /
        (Γ * ρ).trace.re) ≤ 2 * M) ∧
    Real.log (rate D Γ) ≤ 2 * M ∧
    Real.log X = (1 - 2 * Real.sqrt (ε * (1 - ε))) / zeta ε ∧
    zeta ε < 58 ∧
    (1 - 2 * Real.sqrt (ε * (1 - ε))) / (2 * zeta ε * M) ≤ Real.logb (rate D Γ) X ∧
    Tpm / zeta ε ≤ (1 - 2 * Real.sqrt (ε * (1 - ε))) / (2 * zeta ε * M) ∧
    ENNReal.ofReal (Tpm / 58) ≤ ENNReal.ofReal (Tpm / zeta ε) ∧
    ENNReal.ofReal (Tpm / 58) ≤ madv μ D (fun x y => f x = y) ε lam η := by sorry

end SelectiveDPT
