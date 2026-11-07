-- Prove2me | Theorems.Thm_QPSpinParisi_eq_3_29_30
-- name    : QPSpinParisi.eq_3_29_30
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:21:39.296708+00:00
-- url     : https://prove2.me/theorems/1a4020ef-001a-4ea0-91d3-d88aebe1d8d5
-- title:
--   Eqs. (3.29)–(3.30) — the mass bound and compactness of $\gamma_{\xi,\beta}$, with a possible atom at $1$
-- statement:
--   Let $\gamma_{\xi,\beta}=\beta\alpha_{\xi,\beta}$ for $\alpha_{\xi,\beta}$ the minimizers of Lemma 3.5. There are $\beta_0>0$ and $C$ such that for every $\beta\ge\beta_0$,
--   $$\int_0^1\gamma_{\xi,\beta}(q)\,dq\le C,\tag{3.29}$$
--   and $\gamma_{\xi,\beta}(t)\le C/(1-t)$ for every $t<1$. Along every sequence $\beta\to\infty$ there are a subsequence, a function $\gamma\in\mathcal U$ and $\upsilon\ge0$ such that $\gamma_{\xi,\beta}(q)\to\gamma(q)$ at every continuity point $q<1$ and
--   $$\zeta(q)\gamma_{\xi,\beta}(q)\,dq\Longrightarrow\zeta(q)\gamma(q)\,dq+\upsilon\delta_1(dq).\tag{3.30}$$
--   The test function $f(q)=q$ gives (3.31). This extracts the limiting order parameter and the mass that may escape to $q=1$.
--
--   Differences from the source:
--   - generalization: one Brownian motion $B$ on an unnamed space → every `BrownianNoise`, on every probability space; reason: the source's $B$ is one such object, and `exists_noise` makes the statement non-vacuous
--   - generalization: $Y_n$ built as $\sum_pc_pY_{n,p}$ → every centered Gaussian field with covariance $n\xi(q(s,t))$ and continuous paths; reason: only the covariance is used; the source's field is one such field, and `exists_overlapField` makes the statement non-vacuous
--   - encoding: weak convergence of measures on $[0,1]$ → convergence of integrals against every $f$ continuous on $[0,1]$; reason: the definition of weak convergence
--   - reading: "every continuity point $q<1$" → continuity points of the extension of $\gamma$ by $0$; reason: the usual convention for Helly's theorem: for $0<q<1$ this is continuity of $\gamma$, and $q=0$ counts exactly when $\gamma(0)=0$, since at $q=0$ one-sided continuity is automatic and Helly's theorem gives nothing there
--   - encoding: the unique family $\alpha_{\xi,\beta}$ → any family of minimizers; reason: by Lemma 3.5 there is only one
-- source:
--   Bhattacharya, Parisi formula and product-state optimization of quantum mixed p-spin Hamiltonians, manuscript (STOC 2027 submission; held version sha256 ae3fccd2…), Eqs. (3.29)–(3.30), p.22 (PDF p.22)

import Mathlib
import Definitions.Def_QPSpinParisi_MixHyp
import Definitions.Def_QPSpinParisi_IsMinB
import Definitions.Def_QPSpinParisi_USet
import Definitions.Def_QPSpinParisi_gamBeta
import Definitions.Def_QPSpinParisi_gamHat
import Definitions.Def_QPSpinParisi_zeta

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal Matrix

namespace QPSpinParisi

/-- Bhattacharya, *Parisi formula and product-state optimization of quantum mixed p-spin Hamiltonians*, manuscript (STOC 2027 submission; held version sha256 ae3fccd2…), Eqs. (3.29)–(3.30), p.22, PDF p.22. For minimizers `α_{ξ,β}` of Lemma 3.5: `sup_{β≥β₀} ∫₀¹ γ_{ξ,β} < ∞` (3.29), `γ_{ξ,β}(t) ≤ C/(1-t)`,
and along every sequence `β → ∞` there are a subsequence, `γ ∈ U` and `υ ≥ 0` with `γ_{ξ,β}(q) → γ(q)` at every continuity point `q < 1` and
`ζ(q) γ_{ξ,β}(q) dq ⇒ ζ(q) γ(q) dq + υ δ₁(dq)` (3.30).

**Formalization Note** Weak convergence on `[0,1]` is written with test functions `f`, continuous on `[0,1]`. The case `f(q) = q` gives (3.31). A continuity point is one of the extension of `γ` by `0`, the
usual convention for Helly's theorem. For `0 < q < 1` this is continuity of `γ` at `q`, and `q = 0` is a continuity point exactly when `γ(0) = 0`. -/
theorem eq_3_29_30 (c : ℕ → ℝ) (hc : MixHyp c) (W : BrownianNoise c) (al : ℝ → Icc (0 : ℝ) 1 → ℝ)
    (hal : ∀ β : ℝ, 0 < β → IsMinB W β (al β)) :
    (∃ β₀ : ℝ, 0 < β₀ ∧ ∃ C : ℝ, ∀ β, β₀ ≤ β →
      (∫ q in (0 : ℝ)..1, gamHat (gamBeta β (al β)) q) ≤ C ∧
      ∀ t : Ico (0 : ℝ) 1, gamBeta β (al β) t ≤ C / (1 - t)) ∧
    ∀ βs : ℕ → ℝ, Tendsto βs atTop atTop →
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ γ ∈ USet, ∃ υ : ℝ, 0 ≤ υ ∧
        (∀ q : Ico (0 : ℝ) 1, ContinuousAt (gamHat γ) q →
          Tendsto (fun k => gamBeta (βs (φ k)) (al (βs (φ k))) q) atTop (𝓝 (γ q))) ∧
        ∀ f : ℝ → ℝ, ContinuousOn f (Icc 0 1) →
          Tendsto (fun k => ∫ q in (0 : ℝ)..1, f q * zeta c q * gamHat (gamBeta (βs (φ k)) (al (βs (φ k)))) q)
            atTop (𝓝 ((∫ q in (0 : ℝ)..1, f q * zeta c q * gamHat γ q) + υ * f 1)) := by sorry

end QPSpinParisi
