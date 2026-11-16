-- Prove2me | Theorems.Thm_QuadSDE_Supplement_theorem_4
-- name    : QuadSDE.Supplement.theorem_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T01:13:48.12124+00:00
-- url     : https://prove2.me/theorems/b0b3be40-6e4f-4434-a50a-e6a69b2968b8
-- title:
--   Theorem 4 — Kolmogorov equation: the Hermite series (52) converges with all derivatives, is the smooth density of $\tilde X(t)$ and solves (54)
-- statement:
--   Let the drift $f$ be admissible (symmetric coefficients, norm and volume preserving) with strength at most $J>0$ and at most $r\ge1$ channels, let $0<p,q\le1$, $T\ge0$ and $Y\in\mathbb R^N$, and let $X$ solve
--   $$dX(t)=f(X(t))\,dt+\sqrt q\,dW(t),\qquad X(0)=Y+\sqrt p\,Z.$$
--   Let $\psi_k$ ($k\ge2$) solve the projected evolution (36) and let $\psi(t)$ be their limit in the Fock space for $t\in[0,T]$. With $\rho(t)=p+qt$, $\lambda(t)=q/(2\rho(t))$, $y=Y/\sqrt p$, $\tilde X(t)=X(t)/\sqrt{\rho(t)}$ and the standard Gaussian density $\mu$, set
--   $$h(t,x)=\sum_{\mathbf m\neq0}\psi_{\mathbf m}(t)H_{\mathbf m}(x),\qquad\tilde\pi_t(x)=\mu(x)\big(1+h(t,x)\big)\qquad(52),$$
--   and let $h_k$ be the projected Hermite sums built from $\psi_k$. Then:
--   1. for every compact $B\subset\mathbb R^N$ and every order $j$, the series of $j$-th spatial derivatives $\sum_{\mathbf m}\psi_{\mathbf m}(t)D^jH_{\mathbf m}(x)$ converges absolutely and uniformly on $[0,T]\times B$, to $D^j_xh(t,x)$;
--   2. the same holds after one time derivative together with any number $j$ of spatial derivatives, and the sum is the time derivative of $D^j_xh$;
--   3. for every $t\in[0,T]$, $\tilde\pi_t$ is a density of $\tilde X(t)$, it is nonnegative everywhere and smooth in $x$, and $t\mapsto\tilde\pi_t(x)$ is continuously differentiable on $[0,T]$;
--   4. for every $x\in\mathbb R^N$ and $t\in[0,T]$, with one-sided time derivatives at the endpoints,
--   $$\partial_t\tilde\pi_t=\lambda(t)\big[\Delta\tilde\pi_t+\nabla\cdot(x\tilde\pi_t)\big]-\sqrt{\rho(t)}\,f\cdot\nabla\tilde\pi_t\qquad(54),$$
--   and $\tilde\pi_0(x)=\mu(x-y)$;
--   5. the projected Hermite sums converge locally uniformly with the same derivatives: $D^j_xh_k\to D^j_xh$ and $\partial_tD^j_xh_k\to\partial_tD^j_xh$ uniformly on $[0,T]\times B$.
--
--   Lemma 7 identifies the series with the density only almost everywhere and in $L^2(\mu)$; this theorem makes the density a classical solution of the Fokker–Planck equation of the rescaled process.
--
--   Differences from the source:
--   - reading: converges absolutely and uniformly on [0, T] × B → the signed partial sums and the partial sums of norms both converge uniformly on [0, T] × B, along the net of finite sets of multi-indices; reason: reading S1 of the plan; the series is indexed by an unordered set of multi-indices
--   - reading: the same holds after spatial derivatives / after one time derivative; "differentiating the Hermite expansion term by term" (proof, p. 25) → the limits of the differentiated series are stated to be the derivatives of the sum h (iterated Fréchet derivatives D^j_x, j ≥ 0, and derivatives within [0, T] in t); reason: what the theorem uses the convergence for; locally uniform convergence of the differentiated series implies it
--   - reading: the resulting PDF π̃_t(x) → the series function μ(1 + h) itself, at every point, is a density of the law of X̃(t) for every t ∈ [0, T]; reason: reading S1; no density, L² or Lemma 7 hypothesis is assumed
--   - reading: the projected Hermite sums → h_k(t, x) = Σ_m (ψ_k)_m(t) H_m(x), converging with their spatial derivatives and with their time derivatives to those of h; reason: the proof (p. 25) applies the estimates to ψ_k and ψ'_k; multiplying by the smooth μ is equivalent on compact sets
--   - encoding: ψ_m(t), complex Fock coefficients → their real parts; reason: ψ_k(0) is real and the projected dynamics is real, so every ψ_m(t) is real (Lemma 7); same instances
--   - encoding: ψ(t) the limit of Theorem 3; X the strong solution → any family of solutions of (36) for k ≥ 2 and ψ(t) their pointwise Fock limit on [0, T]; X any pathwise solution of Eq. (2) on every horizon (binders of the published QuadSDE.lemma_7); reason: (36) has unique solutions and pathwise solutions agree a.s. with the strong one; same instances
-- source:
--   Bravyi, Byrne, Zayats, Zhuk, Zlokapa, Quantum algorithms for stochastic nonlinear differential equations, arXiv:2606.08349 (sha256 29bd9b01…94cdf), §4.4, Theorem 4, p. 25

import Mathlib
import Definitions.Def_QuadSDE_DriftClass
import Definitions.Def_QuadSDE_NoisySDE
import Definitions.Def_QuadSDE_Frame
import Definitions.Def_QuadSDE_GaussHermite
import Definitions.Def_QuadSDE_Fock
import Definitions.Def_QuadSDE_Kolmogorian
import Definitions.Def_QuadSDE_Supplement_Kolmogorov

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal

namespace QuadSDE.Supplement

/-- **Theorem 4 (Kolmogorov equation).**
Bravyi, Byrne, Zayats, Zhuk, Zlokapa, *Quantum algorithms for stochastic nonlinear differential
equations*, arXiv:2606.08349 (sha256 29bd9b01…), §4.4, Theorem 4, p. 25: "The series in Eq. (52)
converges absolutely and uniformly on `[0, T] × B` for every compact `B ⊂ ℝ^N`. The same holds after
any fixed number of spatial derivatives, and after one time derivative together with any fixed
number of spatial derivatives. The resulting PDF `π̃_t(x)` is nonnegative, continuously
differentiable in time, and smooth in space. It satisfies
`∂_t π̃_t = λ(t)[Δπ̃_t + ∇ · (x π̃_t)] − √ρ(t) f · ∇π̃_t` (54)
for every `x ∈ ℝ^N` and `t ∈ [0, T]`, with initial density `µ(x − y)` and one-sided time
derivatives at the endpoints. The projected Hermite sums converge locally uniformly with the same
derivatives."

Setting of §4 (as in `QuadSDE.lemma_7`): an admissible drift `c` with strength `≤ J`, `J > 0`, and
`≤ r` channels, `r ≥ 1`; `0 < p, q ≤ 1`; `T ≥ 0`; the noise `(W, Z)`; `X` solving Eq. (2) with
`X(0) = Y + √p Z` on every horizon; `ψ_k` (`k ≥ 2`) solving the projected evolution (36); and `ψ(t)`
their limit in the Fock space for every `t ∈ [0, T]`. Write `a_m(t) = ψ_m(t)` (`m ≠ 0`, `a_0 = 0`),
`h(t, x) = Σ_m a_m(t) H_m(x)`, `π̃_t(x) = µ(x)(1 + h(t, x))`, and `h_k(t, x) = Σ_m a^k_m(t) H_m(x)` the
projected Hermite sums built from `ψ_k`. Then there are functions `a'_m(t)`, the time derivatives of
`a_m` within `[0, T]`, such that:
1. for every compact `B` and every `j`, the `j`-th spatial derivatives `Σ_m a_m(t) D^j H_m(x)` of the
   series converge uniformly on `[0, T] × B` (along finite sets of multi-indices) to `D^j_x h(t, x)`,
   and so do the partial sums of their norms;
2. for every compact `B` and every `j`, the series `Σ_m a'_m(t) D^j H_m(x)` (one time derivative and
   `j` spatial derivatives) converges uniformly on `[0, T] × B`, absolutely likewise, and its sum is
   the time derivative within `[0, T]` of `D^j_x h(t, x)`;
3. for every `t ∈ [0, T]`, `π̃_t` is a density of `X̃(t) = X(t)/√ρ(t)`, `π̃_t(x) ≥ 0` for every `x`, and
   `π̃_t` is `C^∞` in `x`; for every `x`, `t ↦ π̃_t(x)` is `C¹` on `[0, T]`;
4. Eq. (54) holds at every `x` and every `t ∈ [0, T]`, with one-sided derivatives at the endpoints,
   and `π̃_0(x) = µ(x − y)` with `y = Y/√p`;
5. for every compact `B` and every `j`, `D^j_x h_k → D^j_x h` uniformly on `[0, T] × B`, and the time
   derivatives of `D^j_x h_k` converge uniformly on `[0, T] × B` to the series of clause 2.

**Formalization Note.** "Absolutely and uniformly" is read as: both the signed partial sums and the
partial sums of norms converge uniformly, along the net of finite sets of multi-indices. Spatial
derivatives are iterated Fréchet derivatives `iteratedFDeriv ℝ j` in `x` (all `j`, including
`j = 0`); the limit of the differentiated series is stated to be the derivative of the sum, which is
what "differentiating the Hermite expansion term by term" asserts. Time derivatives are
derivatives within `[0, T]` (one-sided at the endpoints). The coefficients are the real parts of
`ψ_m(t)` (Lemma 7 shows they are real), as in `QuadSDE.lemma_7`. "The resulting PDF" is the series
function itself, everywhere, and is a density of the law of `X̃(t)`; no density, `L²` or Lemma 7
hypothesis is assumed. For `T = 0` the time-derivative clauses on the one-point interval are
degenerate, as they are in the source. -/
theorem theorem_4 {N : ℕ} (c : Coeff N) (hc : IsAdmissibleDrift c) (J : ℝ) (hJ0 : 0 < J)
    (hJ : strengthLE c J) (r : ℕ) (hr0 : 1 ≤ r) (hr : channelsLE c r) (p q T : ℝ) (hp : 0 < p)
    (hp1 : p ≤ 1) (hq : 0 < q) (hq1 : q ≤ 1) (hT : 0 ≤ T) (Y : Fin N → ℝ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → Fin N → ℝ) (Z : Ω → Fin N → ℝ) (hBZ : NoiseSetting P B Z)
    (X : ℝ≥0 → Ω → Fin N → ℝ)
    (hX : ∀ T' : ℝ≥0, SolvesPathwise P (drift c) q B (fun ω => Y + Real.sqrt p • Z ω) X T')
    (ψs : ℕ → ℝ → Fock N) (hψs : ∀ k, 2 ≤ k → IsProjSol c p q Y T k (ψs k))
    (ψ : ℝ → Fock N) (hψ : ∀ t ∈ Set.Icc (0 : ℝ) T, Tendsto (fun k => ψs k t) atTop (𝓝 (ψ t))) :
    ∃ a' : MIdx N → ℝ → ℝ,
      (∀ m : MIdx N, ∀ t ∈ Set.Icc (0 : ℝ) T,
        HasDerivWithinAt (fun s => coeffRe (ψ s) m) (a' m t) (Set.Icc 0 T) t) ∧
      -- 1. the series and all its spatial derivatives: absolute and uniform convergence on compacts
      (∀ K : Set (Fin N → ℝ), IsCompact K → ∀ j : ℕ,
        TendstoUniformlyOn
          (fun (F : Finset (MIdx N)) (z : ℝ × (Fin N → ℝ)) =>
            ∑ m ∈ F, coeffRe (ψ z.1) m • iteratedFDeriv ℝ j (hermiteMulti m) z.2)
          (fun z => iteratedFDeriv ℝ j (fun x => hermiteSum (coeffRe (ψ z.1)) x) z.2)
          atTop (Set.Icc 0 T ×ˢ K) ∧
        ∃ A : ℝ × (Fin N → ℝ) → ℝ,
          TendstoUniformlyOn
            (fun (F : Finset (MIdx N)) (z : ℝ × (Fin N → ℝ)) =>
              ∑ m ∈ F, ‖coeffRe (ψ z.1) m • iteratedFDeriv ℝ j (hermiteMulti m) z.2‖)
            A atTop (Set.Icc 0 T ×ˢ K)) ∧
      -- 2. one time derivative together with any spatial derivatives
      (∀ K : Set (Fin N → ℝ), IsCompact K → ∀ j : ℕ,
        TendstoUniformlyOn
          (fun (F : Finset (MIdx N)) (z : ℝ × (Fin N → ℝ)) =>
            ∑ m ∈ F, a' m z.1 • iteratedFDeriv ℝ j (hermiteMulti m) z.2)
          (fun z => ∑' m : MIdx N, a' m z.1 • iteratedFDeriv ℝ j (hermiteMulti m) z.2)
          atTop (Set.Icc 0 T ×ˢ K) ∧
        (∃ A : ℝ × (Fin N → ℝ) → ℝ,
          TendstoUniformlyOn
            (fun (F : Finset (MIdx N)) (z : ℝ × (Fin N → ℝ)) =>
              ∑ m ∈ F, ‖a' m z.1 • iteratedFDeriv ℝ j (hermiteMulti m) z.2‖)
            A atTop (Set.Icc 0 T ×ˢ K)) ∧
        ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x ∈ K,
          HasDerivWithinAt
            (fun s => iteratedFDeriv ℝ j (fun y => hermiteSum (coeffRe (ψ s)) y) x)
            (∑' m : MIdx N, a' m t • iteratedFDeriv ℝ j (hermiteMulti m) x) (Set.Icc 0 T) t) ∧
      -- 3. the resulting PDF: density of the rescaled process, nonnegative, smooth, C¹ in time
      (∀ t ∈ Set.Icc (0 : ℝ) T,
        P.map (fun ω => (Real.sqrt (rho p q t))⁻¹ • X t.toNNReal ω) =
          volume.withDensity (fun x =>
            ENNReal.ofReal (gaussDensity x * (1 + hermiteSum (coeffRe (ψ t)) x)))) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x : Fin N → ℝ,
        0 ≤ gaussDensity x * (1 + hermiteSum (coeffRe (ψ t)) x)) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) T,
        ContDiff ℝ (⊤ : ℕ∞) (fun x => gaussDensity x * (1 + hermiteSum (coeffRe (ψ t)) x))) ∧
      (∀ x : Fin N → ℝ,
        ContDiffOn ℝ 1 (fun t => gaussDensity x * (1 + hermiteSum (coeffRe (ψ t)) x))
          (Set.Icc 0 T)) ∧
      -- 4. the Kolmogorov forward equation (54) and the initial density µ(x − y)
      (∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x : Fin N → ℝ,
        HasDerivWithinAt (fun s => gaussDensity x * (1 + hermiteSum (coeffRe (ψ s)) x))
          (kolmogorovRHS c p q t
            (fun z => gaussDensity z * (1 + hermiteSum (coeffRe (ψ t)) z)) x)
          (Set.Icc 0 T) t) ∧
      (∀ x : Fin N → ℝ,
        gaussDensity x * (1 + hermiteSum (coeffRe (ψ 0)) x) = gaussDensity (x - yvec p Y)) ∧
      -- 5. the projected Hermite sums converge locally uniformly with the same derivatives
      (∀ K : Set (Fin N → ℝ), IsCompact K → ∀ j : ℕ,
        TendstoUniformlyOn
          (fun (k : ℕ) (z : ℝ × (Fin N → ℝ)) =>
            iteratedFDeriv ℝ j (fun x => hermiteSum (coeffRe (ψs k z.1)) x) z.2)
          (fun z => iteratedFDeriv ℝ j (fun x => hermiteSum (coeffRe (ψ z.1)) x) z.2)
          atTop (Set.Icc 0 T ×ˢ K) ∧
        ∃ dk : ℕ → ℝ × (Fin N → ℝ) →
            ContinuousMultilinearMap ℝ (fun _ : Fin j => Fin N → ℝ) ℝ,
          (∀ k, 2 ≤ k → ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x ∈ K,
            HasDerivWithinAt
              (fun s => iteratedFDeriv ℝ j (fun y => hermiteSum (coeffRe (ψs k s)) y) x)
              (dk k (t, x)) (Set.Icc 0 T) t) ∧
          TendstoUniformlyOn dk
            (fun z => ∑' m : MIdx N, a' m z.1 • iteratedFDeriv ℝ j (hermiteMulti m) z.2)
            atTop (Set.Icc 0 T ×ˢ K)) := by sorry

end QuadSDE.Supplement
