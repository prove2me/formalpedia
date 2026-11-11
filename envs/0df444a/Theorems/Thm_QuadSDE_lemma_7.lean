-- Prove2me | Theorems.Thm_QuadSDE_lemma_7
-- name    : QuadSDE.lemma_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:18:24.395725+00:00
-- url     : https://prove2.me/theorems/4ad9b9a3-da69-42f9-8620-50bbeafeb576
-- title:
--   Lemma 7 — $\psi_{\mathbf m}(t)=\langle H_{\mathbf m},h_t\rangle_\mu$, the Hermite series of $h_t$ converges in $L^2(\mu)$, $\|\psi(t)\|=\|h_t\|_{L^2(\mu)}\le R_0$
-- statement:
--   Assume the setting of APX-SDE: an admissible drift with strength at most $J>0$ and at most $r\ge1$ channels, $0<p,q\le1$, $T\ge0$, the noise $(W,Z)$, and $X$ solving Eq. (2) with $X(0)=Y+\sqrt pZ$ on every horizon. For $k\ge2$ let $\psi_k$ solve the projected evolution (36), and let $\psi(t)$ be the limit of $\psi_k(t)$ in $\mathcal F$ for every $t\in[0,T]$ (Theorem 3). Let $h_t\in L^2(\mu)$, $t\ge0$, be functions with $1+h_t\ge0$ almost everywhere such that $\tilde X(t)=X(t)/\sqrt{\rho(t)}$ has density $\mu(1+h_t)$ for every $t$ (Lemma 4). Then for every $t\in[0,T]$:
--   1. $\psi(t)$ is the vector of Hermite coefficients of $h_t$:
--   $$\psi_{\mathbf m}(t)=\langle H_{\mathbf m},h_t\rangle_\mu\qquad\text{for all }\mathbf m\ne0;$$
--   2. the series $\sum_{\mathbf m\ne0}\psi_{\mathbf m}(t)H_{\mathbf m}$ converges to $h_t$ in $L^2(\mu)$, so that
--   $$\tilde\pi_t(x)=\mu(x)\Big[1+\sum_{\mathbf m\ne0}\psi_{\mathbf m}(t)H_{\mathbf m}(x)\Big]\qquad(52)$$
--   almost everywhere;
--   3. $\|\psi(t)\|=\|h_t\|_{L^2(\mu)}\le R_0$.
--
--   This links the linear Fock-space evolution to the law of the nonlinear SDE.
--
--   Differences from the source:
--   - generalization: ψ(t) from Theorem 3 (uniform limit); h_t from Lemma 4 → any pointwise Fock-norm limit ψ(t) of solutions ψ_k(t) of (36), t ∈ [0, T]; any h_t ∈ L²(μ) with 1 + h_t ≥ 0 a.e. and P.map X̃(t) = μ(1 + h_t) dx for all t ≥ 0; reason: Theorem 3's ψ and Lemma 4's h are special cases
--   - generalization: X(t) solves the SDE Eq. (2) ("a unique global strong solution", p. 17) → any process X on any probability space carrying (W, Z) that solves Eq. (2) pathwise (continuous paths, integral equation a.s.); reason: with additive noise and a locally Lipschitz drift every pathwise solution agrees a.s. with the strong solution, so the statement specializes to the source's
--   - reading: (52) almost everywhere, where the series converges in L²(μ) → ∫ (Σ_{m ∈ F, m ≠ 0} ψ_m(t) H_m − h_t)² dμ → 0 as the finite set F of multi-indices grows (unconditional convergence), together with the density hypothesis π̃_t = μ(1 + h_t); reason: an L²(μ) series identity is an a.e. identity of its limit; unconditional convergence contains convergence in any order
--   - encoding: indices in [N], time t ≥ 0 → Fin N (0-based), process time ℝ≥0, ODE time ℝ on [0, T]; reason: Lean convention; same instances
-- source:
--   Bravyi, Byrne, Zayats, Zhuk, Zlokapa, Quantum algorithms for stochastic nonlinear differential equations, arXiv:2606.08349 (sha256 29bd9b01…94cdf), §4.4, Lemma 7, p. 24

import Mathlib
import Definitions.Def_QuadSDE_DriftClass
import Definitions.Def_QuadSDE_NoisySDE
import Definitions.Def_QuadSDE_Frame
import Definitions.Def_QuadSDE_GaussHermite
import Definitions.Def_QuadSDE_Fock
import Definitions.Def_QuadSDE_Kolmogorian

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal

namespace QuadSDE

/-- **Lemma 7 (identification of the Hermite coefficients).**
Bravyi–Byrne–Zayats–Zhuk–Zlokapa, arXiv:2606.08349 (sha256 29bd9b01…), §4.4, Lemma 7, p. 24: "For
every `t ∈ [0, T]`, `ψ(t)` is the vector of Hermite coefficients of the correction function `h_t`
from Lemma 4, that is, `ψ_m(t) = ⟨H_m, h_t⟩_µ` for all `m ≠ 0`. Consequently, the PDF of `X̃(t)`
satisfies `π̃_t(x) = µ(x)[1 + Σ_{m≠0} ψ_m(t)H_m(x)]` (52) almost everywhere, where the series
converges in `L²(µ)`. Moreover, `‖ψ(t)‖ = ‖h_t‖_{L²(µ)} ≤ R₀`."

Setting of APX-SDE (admissible drift with strength `≤ J`, `J > 0`, and `≤ r` channels, `r ≥ 1`;
`0 < p, q ≤ 1`; `T ≥ 0`; noise `(W, Z)`; `X` solving Eq. (2) with `X(0) = Y + √p Z` on every
horizon). Let `ψ_k` (`k ≥ 2`) solve the projected evolution (36), let `ψ(t)` be their limit in the
Fock space for every `t ∈ [0, T]` (Theorem 3), and let `h_t` be any functions in `L²(µ)` with
`1 + h_t ≥ 0` a.e. such that `X̃(t) = X(t)/√ρ(t)` has density `µ(1 + h_t)` for every `t ≥ 0`
(Lemma 4). Then for every
`t ∈ [0, T]`:
1. `ψ_m(t) = ⟨H_m, h_t⟩_µ` for all `m ≠ 0`;
2. the partial sums of `Σ_{m≠0} ψ_m(t) H_m` converge to `h_t` in `L²(µ)` (along finite sets of
   multi-indices, i.e. unconditionally), so that (52) holds almost everywhere;
3. `‖ψ(t)‖ = ‖h_t‖_{L²(µ)} ≤ R₀`.

**Formalization Note.** The `L²(µ)` convergence is stated as `∫ (Σ_{m ∈ F, m ≠ 0} ψ_m H_m − h_t)² dµ → 0`
as the finite set `F` grows; by clause 1 the coefficients are real, and their real parts are used.
Together with the density hypothesis `π̃_t = µ(1 + h_t)`, this is (52). -/
theorem lemma_7 {N : ℕ} (c : Coeff N) (hc : IsAdmissibleDrift c) (J : ℝ) (hJ0 : 0 < J)
    (hJ : strengthLE c J) (r : ℕ) (hr0 : 1 ≤ r) (hr : channelsLE c r) (p q T : ℝ) (hp : 0 < p)
    (hp1 : p ≤ 1) (hq : 0 < q) (hq1 : q ≤ 1) (hT : 0 ≤ T) (Y : Fin N → ℝ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → Fin N → ℝ) (Z : Ω → Fin N → ℝ) (hBZ : NoiseSetting P B Z)
    (X : ℝ≥0 → Ω → Fin N → ℝ)
    (hX : ∀ T' : ℝ≥0, SolvesPathwise P (drift c) q B (fun ω => Y + Real.sqrt p • Z ω) X T')
    (ψs : ℕ → ℝ → Fock N) (hψs : ∀ k, 2 ≤ k → IsProjSol c p q Y T k (ψs k))
    (ψ : ℝ → Fock N) (hψ : ∀ t ∈ Set.Icc (0 : ℝ) T, Tendsto (fun k => ψs k t) atTop (𝓝 (ψ t)))
    (h : ℝ≥0 → (Fin N → ℝ) → ℝ)
    (hdens : ∀ t : ℝ≥0, P.map (fun ω => (Real.sqrt (rho p q t))⁻¹ • X t ω) =
      volume.withDensity (fun x => ENNReal.ofReal (gaussDensity x * (1 + h t x))))
    (hpos : ∀ t : ℝ≥0, ∀ᵐ x ∂(volume : Measure (Fin N → ℝ)), 0 ≤ 1 + h t x)
    (hL2 : ∀ t : ℝ≥0, MemLp (h t) 2 (gaussPi N)) :
    ∀ t ∈ Set.Icc (0 : ℝ) T,
      (∀ m : MIdx N, m ≠ 0 → ψ t m = ((hermiteCoeff (h t.toNNReal) m : ℝ) : ℂ)) ∧
      Tendsto (fun F : Finset (MIdx N) =>
          ∫ x, (∑ m ∈ F, (if m = 0 then 0 else (ψ t m).re * hermiteMulti m x) -
            h t.toNNReal x) ^ 2 ∂gaussPi N) atTop (𝓝 0) ∧
      ‖ψ t‖ = Real.sqrt (∫ x, h t.toNNReal x ^ 2 ∂gaussPi N) ∧
      ‖ψ t‖ ≤ R0 p Y := by sorry

end QuadSDE
