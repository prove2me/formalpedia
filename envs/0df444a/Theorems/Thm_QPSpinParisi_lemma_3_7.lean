-- Prove2me | Theorems.Thm_QPSpinParisi_lemma_3_7
-- name    : QPSpinParisi.lemma_3_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:21:42.315421+00:00
-- url     : https://prove2.me/theorems/0cc8f445-16fd-4537-9ee2-c0a7e98a2df4
-- title:
--   Lemma 3.7 — derivative bounds of $\Phi=\Psi_{\xi,\gamma}$, the identities (3.32), and $\mathbb E\operatorname{Tr}(H_t^2)>0$
-- statement:
--   Fix $\gamma\in\mathcal U$ and $\Phi=\Psi_{\xi,\gamma}$.
--
--   1. For $0<b<1$, the derivatives of $\Phi(t,x)$ in $x$ up to order $4$ exist, are continuous and uniformly bounded for $0\le t\le b$, $x\in\mathbb R^3$.
--   2. $\|\nabla\Phi\|\le1$ and $\nabla^2\Phi\succeq0$.
--   3. Let $X$ solve $dX_t=\zeta(t)\gamma(t)\nabla\Phi(t,X_t)\,dt+\sqrt{\zeta(t)}\,dB_t$, $X_0=0$, and set $H_t=\nabla^2\Phi(t,X_t)$. A solution exists, and for each solution and $0\le a<b<1$,
--   $$\nabla\Phi(b,X_b)-\nabla\Phi(a,X_a)=\int_a^b\sqrt{\zeta(t)}H_t\,dB_t,\quad H_b-H_a=-\int_a^b\zeta(t)\gamma(t)H_t^2\,dt+\sum_{k=1}^3\int_a^b\sqrt{\zeta(t)}\,\partial_kH_t\,dB^k_t.\tag{3.32}$$
--   4. $\mathbb E\operatorname{Tr}(H_t^2)>0$ for every $t\in[0,1)$.
--
--   These facts drive the strict convexity of the Parisi functional.
--
--   Differences from the source:
--   - generalization: one Brownian motion $B$ on an unnamed space → every `BrownianNoise`, on every probability space; reason: the source's $B$ is one such object, and `exists_noise` makes the statement non-vacuous
--   - reading: "Finally, $\mathbb E\operatorname{Tr}(H_t^2)>0$", no range of $t$ → every $t\in[0,1)$; reason: the stronger reading; at $t=0$ it follows from (3.32)
--   - generalization: "Let $X_t$ solve" → a solution exists, and the claims hold for every solution; reason: without existence the claims could be vacuous; the source's $X$ is a solution
--   - encoding: matrix identities with vector Itô integrals → entrywise, with integrals given by `HasBrownianItoIntegral`, the integrand cut to $[a,b]$; reason: the same identities
--   - encoding: the derivatives "w.r.t. $x$" → `ContDiff` and `iteratedFDeriv` of the control value; reason: the same objects
-- source:
--   Bhattacharya, Parisi formula and product-state optimization of quantum mixed p-spin Hamiltonians, manuscript (STOC 2027 submission; held version sha256 ae3fccd2…), Lemma 3.7, p.23 (PDF p.23)

import Mathlib
import Definitions.Def_QPSpinParisi_MixHyp
import Definitions.Def_QPSpinParisi_USet
import Definitions.Def_QPSpinParisi_gradPsi
import Definitions.Def_QPSpinParisi_hessPsi
import Definitions.Def_QPSpinParisi_d3Psi
import Definitions.Def_QPSpinParisi_IsParisiPath

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal Matrix

namespace QPSpinParisi

/-- Bhattacharya, *Parisi formula and product-state optimization of quantum mixed p-spin Hamiltonians*, manuscript (STOC 2027 submission; held version sha256 ae3fccd2…), Lemma 3.7, p.23, PDF p.23. Fix `γ ∈ U` and `Φ = Ψ_{ξ,γ}`. For `0 < b < 1`, the derivatives of `Φ(t, x)` in `x` up to order 4 exist, are
continuous and uniformly bounded for `0 ≤ t ≤ b`, `x ∈ ℝ³`; moreover `‖∇Φ‖ ≤ 1`, `∇²Φ ⪰ 0`. Let `X` solve
`dX_t = ζ(t) γ(t) ∇Φ(t, X_t) dt + √ζ(t) dB_t`, `X₀ = 0`, and `H_t = ∇²Φ(t, X_t)`. For `0 ≤ a < b < 1`, (3.32) holds:
`∇Φ(b, X_b) - ∇Φ(a, X_a) = ∫_a^b √ζ H_t dB_t` and `H_b - H_a = -∫_a^b ζ γ H_t² dt + ∑_k ∫_a^b √ζ ∂_k H_t dB^k_t`. Finally `E Tr(H_t²) > 0`.

**Formalization Note** The identities are stated by entries, each Itô integral given by a process `J` tied to the integrand by
`EthierKurtz.HasBrownianItoIntegral`, with the integrand cut to `[a, b]`, so that `J k b` is `∫_a^b`. Existence of `X` is added, so that
the later clauses are not vacuous, and they hold for every solution. The last clause is read for every `t ∈ [0,1)`. -/
theorem lemma_3_7 (c : ℕ → ℝ) (hc : MixHyp c) (W : BrownianNoise c) (γ : Ico (0 : ℝ) 1 → ℝ) (hγ : γ ∈ USet) :
    (∀ b : ℝ, 0 < b → b < 1 → ∃ C : ℝ,
      (∀ t ∈ Icc 0 b, ContDiff ℝ 4 (Psi W γ t)) ∧
      ∀ k : ℕ, 1 ≤ k → k ≤ 4 →
        ContinuousOn (fun p : ℝ × E3 => iteratedFDeriv ℝ k (Psi W γ p.1) p.2) (Icc 0 b ×ˢ univ) ∧
        ∀ t ∈ Icc 0 b, ∀ x, ‖iteratedFDeriv ℝ k (Psi W γ t) x‖ ≤ C) ∧
    (∀ t ∈ Ico (0 : ℝ) 1, ∀ x, ‖gradPsi W γ t x‖ ≤ 1 ∧ (hessPsi W γ t x).PosSemidef) ∧
    (∃ X, IsParisiPath W γ X) ∧
    ∀ X, IsParisiPath W γ X →
      (∀ a b : ℝ≥0, a < b → b < 1 →
        (∀ i : Fin 3, ∃ J : Fin 3 → ℝ≥0 → W.Ω → ℝ,
          (∀ k, EthierKurtz.HasBrownianItoIntegral W.P W.filt (W.B k)
            (fun t ω => if a ≤ t ∧ t ≤ b then Real.sqrt (zeta c t) * hessPsi W γ t (X t ω) i k else 0) (J k)) ∧
          ∀ᵐ ω ∂W.P, gradPsi W γ b (X b ω) i - gradPsi W γ a (X a ω) i = ∑ k, J k b ω) ∧
        (∀ i j : Fin 3, ∃ J : Fin 3 → ℝ≥0 → W.Ω → ℝ,
          (∀ k, EthierKurtz.HasBrownianItoIntegral W.P W.filt (W.B k)
            (fun t ω => if a ≤ t ∧ t ≤ b then Real.sqrt (zeta c t) * d3Psi W γ t (X t ω) k i j else 0) (J k)) ∧
          ∀ᵐ ω ∂W.P, hessPsi W γ b (X b ω) i j - hessPsi W γ a (X a ω) i j =
            -(∫ t in (a : ℝ)..b, zeta c t * gamHat γ t *
                (hessPsi W γ t (X t.toNNReal ω) * hessPsi W γ t (X t.toNNReal ω)) i j)
              + ∑ k, J k b ω)) ∧
      ∀ t : ℝ≥0, t < 1 →
        Integrable (fun ω => Matrix.trace (hessPsi W γ t (X t ω) * hessPsi W γ t (X t ω))) W.P ∧
        0 < ∫ ω, Matrix.trace (hessPsi W γ t (X t ω) * hessPsi W γ t (X t ω)) ∂W.P := by sorry

end QPSpinParisi
