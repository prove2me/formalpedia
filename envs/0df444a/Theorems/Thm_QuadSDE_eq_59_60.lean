-- Prove2me | Theorems.Thm_QuadSDE_eq_59_60
-- name    : QuadSDE.eq_59_60
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:17:52.671046+00:00
-- url     : https://prove2.me/theorems/bfc122f6-e644-44ff-91a9-ae0412b9e1c0
-- title:
--   Eqs. (59)–(60) — $\mathbb E\,u_0(X(T))=\bar u+\langle\psi_{\mathrm{out}},\psi(T)\rangle$ and $|v-v_k|\le BR_*[\dots]e^{-\theta(\sqrt{k+1}-1)}$, $B\le\sqrt2(1+T)$
-- statement:
--   Assume the setting of APX-SDE as in Lemma 7, with an observable $u_0\in\mathcal O$. For $k\ge2$ let $\psi_k$ solve the projected evolution (36), and let $\psi(T)$ be the limit of $\psi_k(T)$ in the Fock space. Let $\bar u$ and $|\psi_{\mathrm{out}}\rangle$ be given by the table (58), $B=\|\psi_{\mathrm{out}}\|$, $v=\mathbb E\,u_0(X(T))$ and $v_k=\bar u+\langle\psi_{\mathrm{out}},\psi_k(T)\rangle$. Then:
--   1. $u_0(X(T))$ is integrable and
--   $$v=\int\tilde\pi_T(x)\,u_0(\sqrt{\rho(T)}\,x)\,dx=\bar u+\langle\psi_{\mathrm{out}},\psi(T)\rangle\qquad(59);$$
--   2. $|\psi_{\mathrm{out}}\rangle\in\mathcal H_k$ for every $k\ge2$;
--   3. $B\le\sqrt2(1+T)$;
--   4. for every $k\ge2$,
--   $$|v-v_k|\le B\,\|\psi(T)-\psi_k(T)\|\le BR_*\Big[1+\frac{J\sqrt{r\rho(T)}}{\lambda_*}\Big(1+\frac1{e\theta}\Big)\Big]e^{-\theta(\sqrt{k+1}-1)}\qquad(60).$$
--
--   The expected observable is thus a single inner product with the truncated Fock-space evolution, up to an explicit error; this is the quantity the quantum algorithm estimates.
--
--   Differences from the source:
--   - generalization: ψ(T) from Theorem 3 → any Fock-norm limit of ψ_k(T); reason: Theorem 3's ψ(T) is one
--   - generalization: X(t) solves the SDE Eq. (2) ("a unique global strong solution", p. 17) → any process X on any probability space carrying (W, Z) that solves Eq. (2) pathwise (continuous paths, integral equation a.s.); reason: with additive noise and a locally Lipschitz drift every pathwise solution agrees a.s. with the strong solution, so the statement specializes to the source's
--   - reading: v = ∫ π̃_T(x) u₀(√ρ(T) x) dx → v = E u₀(X(T)), the expectation over the probability space, with an explicit integrability clause; reason: the two are equal by Lemma 4; this is the quantity of Problem 2
--   - encoding: ⟨ψ_out, ψ(T)⟩, B = ‖ψ_out‖, |ψ_out⟩ ∈ 𝓗_k → complex inner product Σ_m conj(ψ_out,m) ψ_m and identities in ℂ; B = (Σ_m |ψ_out,m|²)^{1/2}; Π_k ψ_out = ψ_out; reason: same values; the identity holds with zero imaginary part
-- source:
--   Bravyi, Byrne, Zayats, Zhuk, Zlokapa, Quantum algorithms for stochastic nonlinear differential equations, arXiv:2606.08349 (sha256 29bd9b01…94cdf), §4.5, Eqs. (59)–(60), p. 26

import Mathlib
import Definitions.Def_QuadSDE_DriftClass
import Definitions.Def_QuadSDE_Observable
import Definitions.Def_QuadSDE_NoisySDE
import Definitions.Def_QuadSDE_Frame
import Definitions.Def_QuadSDE_Fock
import Definitions.Def_QuadSDE_Kolmogorian
import Definitions.Def_QuadSDE_Readout

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal

namespace QuadSDE

/-- **§4.5, Eqs. (59)–(60), p. 26: the observable as an inner product, and its truncation error.**
Bravyi–Byrne–Zayats–Zhuk–Zlokapa, arXiv:2606.08349 (sha256 29bd9b01…), §4.5, p. 26: "Thus
`|ψ_out⟩ ∈ 𝓗_k` for every `k ≥ 2`, and its norm `B = ‖ψ_out‖` satisfies `B ≤ √2(1 + T)` because
`ρ(T) ≤ 1 + T`. Orthonormality of the Hermite polynomials and Lemma 7 imply
`v = ∫ π̃_T(x) u₀(√ρ(T) x) dx = ū + ⟨ψ_out, ψ(T)⟩`, `v_k = ū + ⟨ψ_out, ψ_k(T)⟩`. (59) Consequently,
Cauchy–Schwarz and Eq. (45) give
`|v − v_k| ≤ B‖ψ(T) − ψ_k(T)‖ ≤ BR_* [1 + (J√(rρ(T))/λ_*)(1 + 1/(eθ))] e^{−θ(√(k+1) − 1)}`. (60)"

Setting of APX-SDE as in Lemma 7, with an observable `u₀ ∈ 𝒪`. Let `ψ_k` (`k ≥ 2`) solve the
projected evolution (36) and let `ψ(T)` be the limit of `ψ_k(T)` in the Fock space. With `ū` and
`ψ_out` from the table (58), `B = ‖ψ_out‖`, `v = E u₀(X(T))` and `v_k = ū + ⟨ψ_out, ψ_k(T)⟩`:
1. `u₀(X(T))` is integrable, and `v = ū + ⟨ψ_out, ψ(T)⟩` (Eq. (59));
2. `ψ_out ∈ 𝓗_k` for every `k ≥ 2`;
3. `B ≤ √2 (1 + T)`;
4. (Eq. (60)) for every `k ≥ 2`,
   `|v − v_k| ≤ B R_* [1 + (J√(rρ(T))/λ_*)(1 + 1/(eθ))] e^{−θ(√(k+1)−1)}`.

**Formalization Note.** `v` is the expectation `E u₀(X(T))` itself (by Lemma 4 it equals
`∫ π̃_T(x) u₀(√ρ(T) x) dx`); clause 1 is the link from the SDE to the Fock space. The inner product
`⟨ψ_out, ψ⟩ = Σ_m conj(ψ_out,m) ψ_m` and the identity are in `ℂ` (they hold with zero imaginary
part); `ψ_out` has finite support. -/
theorem eq_59_60 {N : ℕ} (c : Coeff N) (hc : IsAdmissibleDrift c) (J : ℝ) (hJ0 : 0 < J)
    (hJ : strengthLE c J) (r : ℕ) (hr0 : 1 ≤ r) (hr : channelsLE c r) (p q T : ℝ) (hp : 0 < p)
    (hp1 : p ≤ 1) (hq : 0 < q) (hq1 : q ≤ 1) (hT : 0 ≤ T) (Y : Fin N → ℝ) (obs : Observable N)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → Fin N → ℝ) (Z : Ω → Fin N → ℝ) (hBZ : NoiseSetting P B Z)
    (X : ℝ≥0 → Ω → Fin N → ℝ)
    (hX : ∀ T' : ℝ≥0, SolvesPathwise P (drift c) q B (fun ω => Y + Real.sqrt p • Z ω) X T')
    (ψs : ℕ → ℝ → Fock N) (hψs : ∀ k, 2 ≤ k → IsProjSol c p q Y T k (ψs k))
    (ψT : Fock N) (hψT : Tendsto (fun k => ψs k T) atTop (𝓝 ψT)) :
    Integrable (fun ω => obs.eval (X T.toNNReal ω)) P ∧
    ((∫ ω, obs.eval (X T.toNNReal ω) ∂P : ℝ) : ℂ) =
      ((ubar obs p q T : ℝ) : ℂ) + fockInner (psiOut obs p q T) ⇑ψT ∧
    (∀ k, 2 ≤ k → Pik k (psiOut obs p q T) = psiOut obs p q T) ∧
    Real.sqrt (∑' m : MIdx N, ‖psiOut obs p q T m‖ ^ 2) ≤ Real.sqrt 2 * (1 + T) ∧
    ∀ k, 2 ≤ k →
      ‖((∫ ω, obs.eval (X T.toNNReal ω) ∂P : ℝ) : ℂ) -
          (((ubar obs p q T : ℝ) : ℂ) + fockInner (psiOut obs p q T) ⇑(ψs k T))‖ ≤
        Real.sqrt (∑' m : MIdx N, ‖psiOut obs p q T m‖ ^ 2) * projErrBound J r p q T Y k := by sorry

end QuadSDE
