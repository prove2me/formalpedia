-- Prove2me | Theorems.Thm_TalagrandThinning_upset_bound_eq_4_1
-- name    : TalagrandThinning.upset_bound_eq_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-12T06:45:41.14253+00:00
-- url     : https://prove2.me/theorems/f90b388f-487e-4170-b730-1199b26e809b
-- title:
--   Eq. (4.1) — the upset bound $\mathbb P(J\cap X_t\in\mathcal U)\le\mu_p(\mathcal U)$
-- statement:
--   Let $0<t,q,p<1$, let $\nu$ be a $q$-spread probability law on $\{0,1\}^N$ with
--
--   $$\eta=\frac{tq(1-p)}{p(1-t)}\le1,$$
--
--   let $\mathcal U$ be increasing, $f=\mathbf 1_{\mathcal U}$, and let $J\sim\nu$ and $X_t\sim\mu_t$ be independent. Then every step of the chain (4.1) holds:
--
--   $$\begin{aligned}\mathbb P(J\cap X_t\in\mathcal U)&\le\mathbb E_\nu\sum_{I\subseteq J}\beta^{2|I|}\hat f_p(I)^2=\sum_{I\subseteq[N]}\beta^{2|I|}\hat f_p(I)^2\,\mathbb P(I\subseteq J)\\&\le\sum_{I\subseteq[N]}(\beta^2q)^{|I|}\hat f_p(I)^2\le\sum_{I\subseteq[N]}\hat f_p(I)^2=\mathbb E_{\mu_p}f^2=\mu_p(\mathcal U),\end{aligned}$$
--
--   and in particular $T_t\nu(\mathcal U)\le\mu_p(\mathcal U)$ for every increasing $\mathcal U$.
--
--   This is the upset form of Theorem 1.2; Strassen's theorem (eq. (1.2)) turns it into the coupling statement $T_t\nu\le_d\mu_p$.
--
--   **Formalization Note** $\mathbb P(J\cap X_t\in\mathcal U)$ is the retention law evaluated at $\mathcal U$; $\mathbb E_\nu g(J)=\sum_J\nu(\{J\})g(J)$. Real quantities are compared with measure values through `ENNReal.ofReal` and `ENNReal.toReal`; all measures here are finite.
--
--   Differences from the source:
--   - encoding: subsets $A\subseteq[N]=\{1,\dots,N\}$, $\cap$, $\subseteq$ → indicator vectors $x:\mathrm{Fin}\,N\to\mathrm{Bool}$ on $\{0,\dots,N-1\}$, $\sqcap$, $\le$; reason: the paper identifies a set with its indicator vector (p.2); relabelling the ground set changes no instance
--   - encoding: expectations $\mathbb E_{\mu_s}$ and laws as random variables → finite weighted sums $\sum_x \mu_s(\{x\})\,f(x)$ and measures on the finite cube; reason: the cube is finite, so expectation is a finite sum; same values
--   - encoding: $\mathcal U$ increasing and $f=\mathbf 1_{\mathcal U}$ → `IsUpperSet U` and `U.indicator (fun _ => 1)`; reason: Mathlib names for the same notions
--   - encoding: the displayed chain (4.1) → one conjunct per step, plus the endpoint inequality; reason: same content, each relation stated separately
-- source:
--   Fang & Wang, A Note on a Result of Chen Li: the Thinning Problem via the Kernel Method, arXiv:2609.18458 (held version dated Sep 12, 2026, sha256 68a0f38d…), proof of Theorem 1.2, eq. (4.1), p.5

import Mathlib
import Definitions.Def_TalagrandThinning_liftL
import Definitions.Def_TalagrandThinning_IsSpread
import Definitions.Def_TalagrandThinning_retention

set_option autoImplicit false

open MeasureTheory

namespace TalagrandThinning

/-- The upset form of Theorem 1.2: the chain (4.1)
(arXiv:2609.18458, held version dated Sep 12, 2026, sha256 68a0f38d…, proof of Theorem 1.2,
eq. (4.1), p.5).

Let `0 < t, q, p < 1`, let `ν` be a `q`-spread probability law on the cube with
`η = tq(1 − p)/(p(1 − t)) ≤ 1`, let `U` be increasing and `f = 1_U`. With `J ∼ ν` and `X_t ∼ µ_t`
independent, every step of (4.1) holds:
(1) `P(J ∩ X_t ∈ U) ≤ E_ν ∑_{I⊆J} β^{2|I|} f̂_p(I)²`;
(2) `E_ν ∑_{I⊆J} β^{2|I|} f̂_p(I)² = ∑_{I⊆[N]} β^{2|I|} f̂_p(I)² P(I ⊆ J)`;
(3) `∑_{I⊆[N]} β^{2|I|} f̂_p(I)² P(I ⊆ J) ≤ ∑_{I⊆[N]} (β²q)^{|I|} f̂_p(I)²`;
(4) `∑_{I⊆[N]} (β²q)^{|I|} f̂_p(I)² ≤ ∑_{I⊆[N]} f̂_p(I)²`;
(5) `∑_{I⊆[N]} f̂_p(I)² = E_{µ_p} f² = µ_p(U)`;
and hence (6) `P(J ∩ X_t ∈ U) ≤ µ_p(U)`.

**Formalization Note** `P(J ∩ X_t ∈ U)` is `T_t ν (U)`, the retention law evaluated at `U`.
`E_ν g(J)` is the finite sum `∑_J ν({J}) g(J)`. Real sums are compared with measures through
`ENNReal.ofReal` and `ENNReal.toReal` (all measures here are finite, so `toReal` loses nothing). -/
theorem upset_bound_eq_4_1 {N : ℕ} (t q p : ℝ) (ht0 : 0 < t) (ht1 : t < 1) (hq0 : 0 < q)
    (hq1 : q < 1) (hp0 : 0 < p) (hp1 : p < 1) (ν : Measure (Cube N)) [IsProbabilityMeasure ν]
    (hν : IsSpread q ν) (hη : t * q * (1 - p) / (p * (1 - t)) ≤ 1)
    (U : Set (Cube N)) (hU : IsUpperSet U) :
    retention t ν U ≤ ENNReal.ofReal (∑ J : Cube N, (ν {J}).toReal *
        ∑ I ∈ (Finset.univ.filter (fun i => J i = true)).powerset,
          beta t p ^ (2 * I.card) * fourierCoeff p (U.indicator (fun _ => (1 : ℝ))) I ^ 2) ∧
    (∑ J : Cube N, (ν {J}).toReal *
        ∑ I ∈ (Finset.univ.filter (fun i => J i = true)).powerset,
          beta t p ^ (2 * I.card) * fourierCoeff p (U.indicator (fun _ => (1 : ℝ))) I ^ 2) =
      ∑ I : Finset (Fin N), beta t p ^ (2 * I.card) *
        fourierCoeff p (U.indicator (fun _ => (1 : ℝ))) I ^ 2 *
          (ν {J : Cube N | ∀ i ∈ I, J i = true}).toReal ∧
    (∑ I : Finset (Fin N), beta t p ^ (2 * I.card) *
        fourierCoeff p (U.indicator (fun _ => (1 : ℝ))) I ^ 2 *
          (ν {J : Cube N | ∀ i ∈ I, J i = true}).toReal) ≤
      ∑ I : Finset (Fin N),
        (beta t p ^ 2 * q) ^ I.card * fourierCoeff p (U.indicator (fun _ => (1 : ℝ))) I ^ 2 ∧
    (∑ I : Finset (Fin N),
        (beta t p ^ 2 * q) ^ I.card * fourierCoeff p (U.indicator (fun _ => (1 : ℝ))) I ^ 2) ≤
      ∑ I : Finset (Fin N), fourierCoeff p (U.indicator (fun _ => (1 : ℝ))) I ^ 2 ∧
    ∑ I : Finset (Fin N), fourierCoeff p (U.indicator (fun _ => (1 : ℝ))) I ^ 2 =
      expect p (fun x => U.indicator (fun _ => (1 : ℝ)) x ^ 2) ∧
    expect p (fun x => U.indicator (fun _ => (1 : ℝ)) x ^ 2) = (prodLaw N p U).toReal ∧
    retention t ν U ≤ prodLaw N p U := by sorry

end TalagrandThinning
