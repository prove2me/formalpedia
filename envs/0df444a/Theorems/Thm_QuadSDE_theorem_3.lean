-- Prove2me | Theorems.Thm_QuadSDE_theorem_3
-- name    : QuadSDE.theorem_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:18:06.029209+00:00
-- url     : https://prove2.me/theorems/54ff43e4-4f4d-4bf2-9b96-3a61b28ea984
-- title:
--   Theorem 3 — projection error: $\psi_k\to\psi$ uniformly, $\|\psi(t)-\psi_k(t)\|\le R_*[1+\frac{J\sqrt{r\rho(T)}}{\lambda_*}(1+\frac1{e\theta})]e^{-\theta(\sqrt{k+1}-1)}$, uniqueness
-- statement:
--   Let the drift be admissible with strength at most $J>0$ and at most $r\ge1$ channels, $0<p,q\le1$, $T\ge0$, $Y\in\mathbb R^N$, and for every $k\ge2$ let $\psi_k$ solve the projected evolution (36). Then there is $\psi:[0,T]\to\mathcal F_0$ such that:
--   1. $\psi_k\to\psi$ uniformly on $[0,T]$ in $\mathcal F_0$;
--   2. for every $k\ge2$ and $0\le t\le T$,
--   $$\|\psi(t)-\psi_k(t)\|\le R_*\Big[1+\frac{J\sqrt{r\rho(T)}}{\lambda_*}\Big(1+\frac1{e\theta}\Big)\Big]e^{-\theta(\sqrt{k+1}-1)}\qquad(45);$$
--   3. $\|\psi(t)\|_S^2\le R_*^2e^{-\lambda_*t}$ for $t\in[0,T]$;
--   4. $\psi\in C^1([0,T],\mathcal F_0)$ solves
--   $$\psi'(t)=K(t)\psi(t),\qquad\psi(0)\text{ given by Eq. (34)}\qquad(46),$$
--   satisfies, for every $t\in[0,T]$,
--   $$\sum_{n\ge1}(n+1)^3\|Q_nv(t)\|^2<\infty,\qquad\lim_{s\to t}\sum_{n\ge1}(n+1)^3\|Q_n(v(s)-v(t))\|^2=0\qquad(47)$$
--   with $v=\psi$, and every $v\in C^1([0,T],\mathcal F_0)$ that solves (46) and satisfies (47) equals $\psi$ on $[0,T]$.
--
--   The constants depend on $J,r,p,q,T$ and $\|Y\|$ but not on $N$: truncating to total degree $k$ costs an error decaying like $e^{-\Omega(\sqrt k)}$.
--
--   Differences from the source:
--   - reading: the sequence ψ_k defined in Eq. (36); ψ is the unique solution among v ∈ C¹([0, T], 𝓕₀) satisfying (47) → any family of solutions of (36) for k ≥ 2; ψ is C¹ on [0, T] in ℓ² with vacuum coefficient 0, solves (46), satisfies (47), and every such v equals ψ on [0, T]; reason: (36) has unique solutions; 'the unique solution among' asserts that ψ belongs to the class
--   - reading: ψ′(t) = K(t)ψ(t); lim_{s→t} → K(t)ψ(t), computed coefficientwise, is the coefficient function of an ℓ² vector that is the derivative of ψ within [0, T]; the limit is taken within [0, T]; reason: ψ is defined on [0, T]; K(t) is unbounded and acts coefficientwise
--   - encoding: sums (39), (47) → sums in [0, ∞]; reason: a divergent sum is ∞, never a junk 0
-- source:
--   Bravyi, Byrne, Zayats, Zhuk, Zlokapa, Quantum algorithms for stochastic nonlinear differential equations, arXiv:2606.08349 (sha256 29bd9b01…94cdf), §4.3, Theorem 3, p. 22

import Mathlib
import Definitions.Def_QuadSDE_DriftClass
import Definitions.Def_QuadSDE_Frame
import Definitions.Def_QuadSDE_Fock
import Definitions.Def_QuadSDE_Kolmogorian

open Filter Topology
open scoped ENNReal

namespace QuadSDE

/-- **Theorem 3 (projection error).**
Bravyi–Byrne–Zayats–Zhuk–Zlokapa, arXiv:2606.08349 (sha256 29bd9b01…), §4.3, Theorem 3, p. 22: "The
sequence of functions `ψ_k(t)` defined in Eq. (36) converges uniformly on `[0, T]` in `𝓕₀` to some
function `ψ(t)`. For every `k ≥ 2` and `0 ≤ t ≤ T`,
`‖ψ(t) − ψ_k(t)‖ ≤ R_* [1 + (J√(rρ(T))/λ_*)(1 + 1/(eθ))] e^{−θ(√(k+1) − 1)}`. (45) Moreover,
`‖ψ(t)‖²_S ≤ R²_* e^{−λ_* t}`, and `ψ` is the unique solution of `ψ′(t) = K(t)ψ(t)`, `ψ(0)` given
by Eq. (34), (46) among functions `v ∈ C¹([0, T], 𝓕₀)` satisfying, for every `t ∈ [0, T]`,
`Σ_{n≥1} (n + 1)³ ‖Q_n v(t)‖² < ∞`, `lim_{s→t} Σ_{n≥1} (n + 1)³ ‖Q_n(v(s) − v(t))‖² = 0`. (47)"

Let the drift be admissible with strength at most `J > 0` and at most `r ≥ 1` channels, let
`0 < p, q ≤ 1`, `T ≥ 0` and `Y ∈ ℝ^N`, and for every `k ≥ 2` let `ψ_k` solve the projected
evolution (36). Then there is `ψ : [0, T] → 𝓕₀` such that
1. `ψ_k → ψ` uniformly on `[0, T]` in the Fock norm;
2. (Eq. (45)) `‖ψ(t) − ψ_k(t)‖ ≤ R_*[1 + (J√(rρ(T))/λ_*)(1 + 1/(eθ))] e^{−θ(√(k+1)−1)}` for every
   `k ≥ 2` and `t ∈ [0, T]`;
3. `‖ψ(t)‖²_S ≤ R²_* e^{−λ_* t}` for `t ∈ [0, T]`;
4. `ψ` is `C¹` on `[0, T]` in `𝓕₀`, solves `ψ′(t) = K(t)ψ(t)` with `ψ(0)` from Eq. (34), satisfies
   (47), and every `v ∈ C¹([0, T], 𝓕₀)` that solves (46) and satisfies (47) equals `ψ` on `[0, T]`.

**Formalization Note.** `𝓕₀` is the Fock space `ℓ²` with vacuum coefficient `0`. Derivatives are
taken in the `ℓ²` norm, one-sided at the endpoints; "`ψ′ = K(t)ψ`" means that the coefficient
function `K(t)ψ(t)` is the coefficient function of an `ℓ²` vector `w` and `w` is the derivative.
The family `(ψ_k)` is any family of solutions of (36); sums (39) and (47) are in `ℝ≥0∞`, and
`lim_{s→t}` is taken within `[0, T]`. -/
theorem theorem_3 {N : ℕ} (c : Coeff N) (hc : IsAdmissibleDrift c) (J : ℝ) (hJ0 : 0 < J)
    (hJ : strengthLE c J) (r : ℕ) (hr0 : 1 ≤ r) (hr : channelsLE c r) (p q T : ℝ) (hp : 0 < p)
    (hp1 : p ≤ 1) (hq : 0 < q) (hq1 : q ≤ 1) (hT : 0 ≤ T) (Y : Fin N → ℝ)
    (ψs : ℕ → ℝ → Fock N) (hψs : ∀ k, 2 ≤ k → IsProjSol c p q Y T k (ψs k)) :
    ∃ ψ : ℝ → Fock N,
      (∀ t ∈ Set.Icc (0 : ℝ) T, ψ t 0 = 0) ∧
      TendstoUniformlyOn ψs ψ atTop (Set.Icc 0 T) ∧
      (∀ k, 2 ≤ k → ∀ t ∈ Set.Icc (0 : ℝ) T, ‖ψ t - ψs k t‖ ≤ projErrBound J r p q T Y k) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) T,
        wNormSq (theta J r p q T) ⇑(ψ t) ≤
          ENNReal.ofReal (Rstar p Y ^ 2 * Real.exp (-(lamStar p q T * t)))) ∧
      ContDiffOn ℝ 1 ψ (Set.Icc 0 T) ∧
      ⇑(ψ 0) = psi0 p Y ∧
      (∀ t ∈ Set.Icc (0 : ℝ) T, ∃ w : Fock N,
        ⇑w = Kop c p q t ⇑(ψ t) ∧ HasDerivWithinAt ψ w (Set.Icc 0 T) t) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) T, cubicNormSq ⇑(ψ t) < ⊤ ∧
        Tendsto (fun s => cubicNormSq (⇑(ψ s) - ⇑(ψ t))) (𝓝[Set.Icc 0 T] t) (𝓝 0)) ∧
      ∀ v : ℝ → Fock N,
        (∀ t ∈ Set.Icc (0 : ℝ) T, v t 0 = 0) →
        ContDiffOn ℝ 1 v (Set.Icc 0 T) →
        ⇑(v 0) = psi0 p Y →
        (∀ t ∈ Set.Icc (0 : ℝ) T, ∃ w : Fock N,
          ⇑w = Kop c p q t ⇑(v t) ∧ HasDerivWithinAt v w (Set.Icc 0 T) t) →
        (∀ t ∈ Set.Icc (0 : ℝ) T, cubicNormSq ⇑(v t) < ⊤ ∧
          Tendsto (fun s => cubicNormSq (⇑(v s) - ⇑(v t))) (𝓝[Set.Icc 0 T] t) (𝓝 0)) →
        ∀ t ∈ Set.Icc (0 : ℝ) T, v t = ψ t := by sorry

end QuadSDE
