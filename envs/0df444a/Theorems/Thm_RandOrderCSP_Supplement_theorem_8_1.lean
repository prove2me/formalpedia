-- Prove2me | Theorems.Thm_RandOrderCSP_Supplement_theorem_8_1
-- name    : RandOrderCSP.Supplement.theorem_8_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T14:27:50.272119+00:00
-- url     : https://prove2.me/theorems/0d84e769-3882-4388-b942-a0c882e51089
-- title:
--   Theorem 8.1 — induction step in expectation
-- statement:
--   Fix integers $q, k \ge 2$ and a $k$-uniform hypergraph $G_*$ with vertex set $\mathcal V_{G_*}$ of size $v_{G_*}$. For $n \ge 1$ let $G_*^n$ be its $n$-fold blowup, with vertex set $\mathcal U := \mathcal V_{G_*^n} = \mathcal V_{G_*} \times [n]$ of size $N := |\mathcal U| = n\, v_{G_*}$, and let $\boldsymbol H \sim \mathrm{Poi}(G_*^n, \alpha n^{-(k-1)})$ be its Poisson sparsification (every edge of $G_*^n$ is copied an independent $\mathrm{Poi}(\alpha n^{-(k-1)})$ number of times). Write $\mathrm{Acy}(\boldsymbol H)$ for the event that the incidence graph of $\boldsymbol H$ is a forest, $\mathcal P_{\boldsymbol H}$ for the partition of $\mathcal U$ into the vertex sets of the connected components of $\boldsymbol H$, and $\mathrm{SF}_{\mathcal P}$ for the sets meeting no block of $\mathcal P$ in exactly one element. For $V \in \mathbb Z_q^{\mathcal U}$, $\mathrm{supp}(V)$ is its set of nonzero coordinates and $\mathrm{wt}(V) = |\mathrm{supp}(V)|$. Fourier coefficients are $\hat f(A) = \mathbb E_{X \in \mathbb Z_q^{\mathcal U}} f(X)\, e^{2\pi i \langle A, X\rangle / q}$, and $\mu_{\mathcal D} = q^N \mathcal D$ is the density of a distribution $\mathcal D$ on $\mathbb Z_q^{\mathcal U}$. The family $\mathcal F_{\mathcal U}(s)$ consists of all $g : \mathbb Z_q^{\mathcal U} \to \mathbb C$ with $\|g\|_1 = \mathbb E_X |g(X)| \le 1$ and $\|g\|_\infty \le q^s$. A distribution $\mathcal D$ is $(\zeta, s)$-bounded when $\sum_{\mathrm{wt}(V) = r} |\hat\mu_{\mathcal D}(V)| \le \mathrm U_{\zeta,s,N}(r)$ for all $0 \le r \le N$, where $\mathrm U_{\zeta,s,N}$ is the Fourier envelope (5.3).
--
--   **Theorem.** There is $\alpha_0 > 0$ such that for every $\zeta \ge 1$ there are $\sigma > 0$ and $\zeta' \ge 1$ with the following property. For all integers $n, s, r \ge 1$, every $\alpha \in (0, \alpha_0)$, and every $(\zeta, s)$-bounded distribution $\mathcal D$ on $\mathbb Z_q^{\mathcal U}$, if $1 \le r \le s \le \sigma n$, then
--
--   $$
--   \mathbb E_{\boldsymbol H}\Big[\, [\![\mathrm{Acy}(\boldsymbol H)]\!] \sup_{g \in \mathcal F_{\mathcal U}(s)} \sum_{\substack{V, Z \in \mathbb Z_q^{\mathcal U} \\ \mathrm{supp}(Z) \in \mathrm{SF}_{\mathcal P_{\boldsymbol H}} \\ \mathrm{wt}(Z - V) = r}} |\hat\mu_{\mathcal D}(V)|\, |\hat g(Z)| \Big] \le \mathrm U_{\zeta', s, N}(r).
--   $$
--
--   The constant $\alpha_0$ depends only on $q$, $k$ and $G_*$; $\sigma$ and $\zeta'$ depend also on $\zeta$, but not on $n$, $s$, $r$, $\alpha$ or $\mathcal D$.
--
--   This is the averaged form of the inductive step of the lower-bound argument: a Fourier-bounded prior, correlated against any bounded test function supported on singleton-free frequencies of an acyclic sparsified blowup, stays within the envelope at a worse but fixed constant. The paper deduces Theorem 5.10 (the high-probability inductive step) from it.
--
--   **Formalization Note** The random hypergraph is `sparsify (blowup G n) c` for a Poisson count vector `c`, and the expectation is a Lebesgue integral over `c` in $[0, \infty]$; the integrand is $0$ off $\mathrm{Acy}$. The supremum is taken in $[0,\infty]$ over the subtype $\mathcal F_{\mathcal U}(s)$ of nonnegative sums, so it is the paper's real supremum (the set is nonempty, containing $g = 0$, and bounded). The summation variable $V$ is named `W` in Lean because `V` is the vertex type of $G_*$. "$(\zeta, s)$-bounded distribution" is `IsDistr D ∧ IsEnvBounded ζ s D`; the published `IsEnvBounded` includes the condition $s \le (e^2 q^4/\zeta^2) N$ under which the paper defines the envelope.
--
--   Differences from the source:
--   - encoding: finite vertex and edge sets, the copy set $[n]$, and a distribution on $\mathbb Z_q^{\mathcal U}$ → `Fintype` carrier/index types, `Fin n`, and a real mass function satisfying `IsDistr`; reason: these are Lean representations of exactly the finite objects on the page, and the `NeZero q` instance needed by Fourier coefficients is derived from $q \ge 2$ rather than assumed.
--   - encoding: (ζ, s)-bounded, with the envelope defined only for s ≤ (e²q⁴/ζ²)N → IsEnvBounded ζ s D includes that inequality as a conjunct; reason: the paper writes U_{ζ,s,N} only on that domain, so a (ζ, s)-bounded distribution satisfies it; σ is chosen after ζ, so no instance the page covers is excluded.
--   - encoding: E_H[[[Acy(H)]] sup_g …] over H ∼ Poi(G^n_∗, αn^{−(k−1)}) → ∫⁻ over the Poisson count vector of (if Acy then ⨆ over the subtype ℱ_U(s) else 0) in ℝ≥0∞; reason: H is a function of the count vector, and the inner sums are nonnegative and bounded, so the ℝ≥0∞ supremum and integral equal the paper's real ones.
-- source:
--   Singer, Tulsiani, Velusamy, A dichotomy theorem for approximating CSPs in random-order streams, STOC 2027 submission (manuscript sha256 3aca9d2f641f5e7b8eccf4c03534efd6e5f17041919320da972b63df1b5148e3), Theorem 8.1, display (8.2), p.35 (PDF p.39)

import Mathlib
import Definitions.Def_RandOrderCSP_optLP
import Definitions.Def_RandOrderCSP_compPartition
import Definitions.Def_RandOrderCSP_blockVol
import Definitions.Def_RandOrderCSP_blowup
import Definitions.Def_RandOrderCSP_poiLaw
import Definitions.Def_RandOrderCSP_fourierCoeff
import Definitions.Def_RandOrderCSP_envelope

set_option autoImplicit false

open MeasureTheory

namespace RandOrderCSP.Supplement

open scoped Classical in
/-- **Theorem 8.1 (induction step in expectation).** Singer, Tulsiani, Velusamy, *A dichotomy theorem for
approximating CSPs in random-order streams*, STOC 2027 submission (manuscript sha256 3aca9d2f…),
Theorem 8.1, p.35 (PDF p.39), display (8.2).

For fixed `q, k ≥ 2` and a `k`-uniform hypergraph `G∗` there is `α₀ > 0` such that for every `ζ ≥ 1`
there are `σ > 0` and `ζ′ ≥ 1` with: for all integers `n, s, r ≥ 1`, every `α ∈ (0, α₀)` and every
`(ζ, s)`-bounded distribution `D` on `ℤ_q^U` (`U = 𝒱_{G∗^n}`), if `1 ≤ r ≤ s ≤ σn` then, for
`H ∼ Poi(G∗^n, αn^{-(k-1)})`,
`E[ [[Acy(H)]] sup_{g ∈ ℱ_U(s)} ∑_{V, Z ∈ ℤ_q^U, supp(Z) ∈ SF_{𝒫_H}, wt(Z − V) = r} |μ̂_D(V)| |ĝ(Z)| ]
  ≤ U_{ζ′,s,N}(r)` with `N = |U| = n · v_{G∗}`.

**Formalization Note.** `H` is `sparsify (blowup G n) c` for a count vector `c ∼ poiLaw` at rate
`poiRate α n k`, and the expectation is the Lebesgue integral over `c` in `ℝ≥0∞`; the integrand is `0`
off `Acy(H)`. The supremum over `ℱ_U(s)` is an `ℝ≥0∞` supremum of the (nonnegative) inner sums, so it
equals the paper's real supremum (that set is nonempty, `g = 0`, and bounded). `μ_D` is
`density D = q^N · D` cast to `ℂ`. "`(ζ, s)`-bounded distribution" is `IsDistr D ∧ IsEnvBounded ζ s D`;
`IsEnvBounded` carries the conjunct `s ≤ (e²q⁴/ζ²)N` of the envelope's printed domain. The
`NeZero q` instance used by the Fourier definitions is derived from `hq`; it is not an additional
hypothesis. `α` ranges over the open interval `(0, α₀)`, as printed. -/
theorem theorem_8_1 {k q : ℕ} (hk : 2 ≤ k) (hq : 2 ≤ q) {V E : Type} [Fintype V]
    [DecidableEq V] [Fintype E] (G : Hypergraph k V E) :
    letI : NeZero q := ⟨by omega⟩
    ∃ α₀ : ℝ, 0 < α₀ ∧
      ∀ ζ : ℝ, 1 ≤ ζ →
        ∃ σ ζ' : ℝ, 0 < σ ∧ 1 ≤ ζ' ∧
          ∀ n s r : ℕ, 1 ≤ n → 1 ≤ s → 1 ≤ r → ∀ α : ℝ, 0 < α → α < α₀ →
            ∀ D : (V × Fin n → ZMod q) → ℝ, IsDistr D → IsEnvBounded ζ s D →
              r ≤ s → (s : ℝ) ≤ σ * n →
              ∫⁻ c, (if (sparsify (blowup G n) c).Acy then
                  ⨆ g : {g : (V × Fin n → ZMod q) → ℂ // InFamilyF (s : ℝ) g},
                    ENNReal.ofReal
                      (∑ W : V × Fin n → ZMod q,
                        ∑ Z ∈ Finset.univ.filter (fun Z : V × Fin n → ZMod q =>
                            IsSF (sparsify (blowup G n) c).compPartition (vsupp Z) ∧
                              wt (Z - W) = r),
                          ‖fourierCoeff (fun X => ((density D X : ℝ) : ℂ)) W‖ *
                            ‖fourierCoeff g.1 Z‖)
                else 0)
                ∂(poiLaw (E × (Fin k → Fin n)) (poiRate α n k)) ≤
                ENNReal.ofReal (envelope q ζ' s (Fintype.card (V × Fin n)) r) := by sorry

end RandOrderCSP.Supplement
