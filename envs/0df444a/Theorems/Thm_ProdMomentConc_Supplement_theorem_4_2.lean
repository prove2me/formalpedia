-- Prove2me | Theorems.Thm_ProdMomentConc_Supplement_theorem_4_2
-- name    : ProdMomentConc.Supplement.theorem_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T14:34:34.914599+00:00
-- url     : https://prove2.me/theorems/cb07a689-dc81-4eed-89e4-671be02a1cf9
-- title:
--   Theorem 4.2 — single-bin and max-load tails for random linear hashing of random keys
-- statement:
--   Let $\mathbb F_q$ be a finite field with $q$ elements, $n=q^\ell$, and view $\mathbb F_q^\ell$ as the set of bins and $U=\mathbb F_q^u\setminus\{0\}$ as the universe of keys. Let $h:\mathbb F_q^u\to\mathbb F_q^\ell$ be a uniformly random linear map, $h(v)=(\langle v,Z^{(1)}\rangle,\dots,\langle v,Z^{(\ell)}\rangle)$ with $Z^{(1)},\dots,Z^{(\ell)}$ independent and uniform on $\mathbb F_q^u$, drawn independently of the random keys $R_1,\dots,R_m\in U$. For a bin $y$ let $L_y=\sum_{i=1}^m\mathbf 1\{h(R_i)=y\}$ and $L_{\max}=\max_y L_y$.
--
--   Let $a,k$ be integers with $1\le k\le a\le m$ and let $\rho_1,\dots,\rho_{k-1}$ be reals. Assume that, for a uniformly random ordered $k$-tuple of distinct indices $i_1,\dots,i_k\in[m]$, sampled independently of the keys,
--   $$\Pr\big[R_{i_{j+1}}\in\mathrm{span}(R_{i_1},\dots,R_{i_j})\ \big|\ i_1,\dots,i_k,R_{i_1},\dots,R_{i_j}\big]\le q^j\rho_j\qquad(j=1,\dots,k-1).$$
--   Then, for every bin $y$,
--   $$\Pr[L_y\ge a]\le\frac{\binom mk}{\binom ak}\,\frac1{n^k}\prod_{j=1}^{k-1}\big(1+(n-1)q^j\rho_j\big),$$
--   and consequently
--   $$\Pr[L_{\max}\ge a]\le\frac{\binom mk}{\binom ak}\,\frac1{n^{k-1}}\prod_{j=1}^{k-1}\big(1+(n-1)q^j\rho_j\big).$$
--
--   The span-hit assumption rules out many linear dependencies among a few sampled keys, which is the only obstruction to treating a random linear hash like a fully random one; with it, the fixed-bin load has the product-moment tail of independent balls up to the factors $1+(n-1)q^j\rho_j$.
--
--   **Formalization Note** One probability space carries the hash matrix $Z$, the keys and the tuple; the tuple is uniform over injective maps $\mathrm{Fin}\,k\to\mathrm{Fin}\,m$ and 0-based. The conditional-probability hypothesis is stated as $\mu(A\cap\{\text{hit}\})\le q^j\rho_j\,\mu(A)$ for every event $A$ of the conditioning σ-algebra. The max-load bound is for the fixed $k$ of the hypothesis.
--
--   Differences from the source:
--   - encoding: h a uniformly random linear map F_q^u → F_q^ℓ, independent of the input sequence; keys R₁, …, R_m ∈ U = F_q^u ∖ {0}; a uniformly random ordered k-tuple sampled independently of the input sequence → one probability space with Z : Ω → (Fin ℓ → Fin u → F) uniform (h(v) c = ∑_d Z c d · v d), R : Fin m → Ω → (Fin u → F) nonzero, ι : Ω → (Fin k → Fin m) with each injective map of probability 1/(m)_k; Z independent of (ι, R) and ι independent of R; reason: the paper's model (§4, p.20: 'ℓ independent uniform vectors Z⁽¹⁾…Z⁽ˡ⁾'); the tuple is a device whose joint law with R is determined by the law of R, and h is drawn independently of everything else
--   - encoding: Pr[R_{i_{j+1}} ∈ span(R_{i_1}, …, R_{i_j}) | i₁, …, i_k, R_{i_1}, …, R_{i_j}] ≤ q^j ρ_j for j = 1, …, k−1 → for j : Fin k with 1 ≤ j and every set S, μ({(ι, R_{ι 0}, …, R_{ι (j−1)}) ∈ S} ∩ {R_{ι j} ∈ span}) ≤ q^j ρ_j μ({(ι, R_{ι 0}, …, R_{ι (j−1)}) ∈ S}); reason: 0-based indexing (ι j is i_{j+1}); a conditional probability is ≤ c almost surely iff this holds for every event of the conditioning σ-algebra, whose events (all values being finite) are exactly these preimages
--   - reading: Pr[L_max ≥ a] ≤ min_{1≤k≤a} (C(m,k)/C(a,k)) n^{−(k−1)} ∏_{j=1}^{k−1}(1 + (n−1)q^jρ_j) → Pr[L_max ≥ a] ≤ (C(m,k)/C(a,k)) n^{−(k−1)} ∏_{j=1}^{k−1}(1 + (n−1)q^jρ_j) for the k of the hypothesis; reason: the span-hit hypothesis is stated for one fixed k, and the union-bound proof gives the bound for that k; the minimum is over the k for which the hypothesis holds, i.e. the minimum of the per-k bounds
--   - encoding: F_q a field with q elements, q ≥ 2 a prime power, n = q^ℓ → a finite field F with Fintype.card F = q and a measurable space with measurable singletons; n written (q : ℝ)^ℓ; reason: every finite field has prime-power order ≥ 2; on a finite type measurable singletons make every set measurable, so no event is excluded
-- source:
--   Saks, Srinivasan, Valieva, Concentration from Product Moments via an Additional Element of Randomness, arXiv:2608.04125 (held version, sha256 5218e9d0405f975413d3e2dd2c4c9d6b43c772029e645965afee1cd619ae38aa), Theorem 4.2, p.21 (PDF p.21); setting §4, pp.19–20 (PDF pp.19–20)

import Mathlib

open MeasureTheory ProbabilityTheory

namespace ProdMomentConc.Supplement

/-- **Theorem 4.2 (single-bin tail for random linear hashing).** Saks, Srinivasan, Valieva,
*Concentration from Product Moments via an Additional Element of Randomness*, arXiv:2608.04125
(held version, sha256 5218e9d0…), Theorem 4.2, p.21 (setting pp.19–20).

Setting (§4, pp.19–20): `F_q` a finite field with `q` elements, `n = q^ℓ` bins `F_q^ℓ`, keys
`R₁, …, Rₘ ∈ U = F_q^u ∖ {0}`, and `h` a uniformly random linear map `F_q^u → F_q^ℓ`, given by `ℓ`
independent uniform vectors `Z⁽¹⁾, …, Z⁽ˡ⁾ ∈ F_q^u` via `h(v) = (⟨v, Z⁽¹⁾⟩, …, ⟨v, Z⁽ˡ⁾⟩)`, independent
of the keys. Fix a bin `y`, let `L_y = ∑ᵢ 1{h(Rᵢ) = y}` and `L_max = max_y L_y`. Let `1 ≤ k ≤ a ≤ m`.
If, for a uniformly random ordered `k`-tuple of distinct indices `i₁, …, i_k ∈ [m]` sampled
independently of the keys,
`Pr[R_{i_{j+1}} ∈ span(R_{i₁}, …, R_{i_j}) | i₁, …, i_k, R_{i₁}, …, R_{i_j}] ≤ q^j ρ_j`
for every `j = 1, …, k − 1`, then
`Pr[L_y ≥ a] ≤ C(m,k)/C(a,k) · n^{−k} · ∏_{j=1}^{k−1} (1 + (n − 1) q^j ρ_j)` and
`Pr[L_max ≥ a] ≤ C(m,k)/C(a,k) · n^{−(k−1)} · ∏_{j=1}^{k−1} (1 + (n − 1) q^j ρ_j)`.

**Formalization Note.**
* One probability space carries the hash matrix `Z` (row `c` is `Z⁽ᶜ⁺¹⁾`), the keys `R` and the
  ordered tuple `ι : Ω → (Fin k → Fin m)`. `Z` is uniform on `F^{ℓ×u}` and independent of
  `(ι, R)`; `ι` is uniform over the injective maps `Fin k → Fin m` (each has probability
  `1/(m)_k`, so `ι` is a.s. injective) and independent of `R`. The tuple is a device of the
  hypothesis; given these laws, the joint law of `(ι, R)` is determined by the law of `R`.
* The tuple is 0-based: `ι j` is the paper's `i_{j+1}`. The span-hit hypothesis for the paper's
  `j` (`1 ≤ j ≤ k − 1`) is stated for `j : Fin k` with `1 ≤ j`: the conditioning σ-algebra is
  generated by `ι` and `R_{ι 0}, …, R_{ι (j−1)}`, and "conditional probability ≤ c a.s." is stated
  as `μ(A ∩ hit) ≤ c μ(A)` for every set `A` of that σ-algebra (all values are finite, so these
  sets are the preimages of arbitrary sets).
* `F` carries a measurable space with measurable singletons (so, being finite, all sets are
  measurable). `q = |F|`, so `q` is a prime power, and `n = q^ℓ` is written `(q : ℝ) ^ ℓ`.
* The max-load bound is stated for the fixed `k` of the hypothesis; the page's
  `min_{1≤k≤a}` is the minimum of these bounds over the `k` for which the hypothesis holds.
* `ρ_j ≥ 0` and `q^j ρ_j ≤ 1` are not assumed (they belong to Definition 4.1, not to this
  theorem). -/
theorem theorem_4_2 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {F : Type*} [Field F] [Fintype F] [DecidableEq F] [MeasurableSpace F]
    [MeasurableSingletonClass F]
    (q : ℕ) (hq : Fintype.card F = q) (u ℓ m : ℕ)
    (Z : Ω → (Fin ℓ → Fin u → F)) (hZm : Measurable Z)
    (hZunif : ∀ A : Fin ℓ → Fin u → F, μ.real {ω | Z ω = A} = 1 / (q : ℝ) ^ (ℓ * u))
    (R : Fin m → Ω → (Fin u → F)) (hRm : ∀ i, Measurable (R i))
    (hRne : ∀ i ω, R i ω ≠ 0)
    (k : ℕ) (ι : Ω → (Fin k → Fin m)) (hιm : Measurable ι)
    (hιunif : ∀ g : Fin k → Fin m, Function.Injective g →
      μ.real {ω | ι ω = g} = 1 / (m.descFactorial k : ℝ))
    (hindZ : IndepFun Z (fun ω => (ι ω, fun i => R i ω)) μ)
    (hindι : IndepFun ι (fun ω => fun i => R i ω) μ)
    (ρ : ℕ → ℝ)
    (hspan : ∀ j : Fin k, 1 ≤ j.val →
      ∀ S : Set ((Fin k → Fin m) × (Fin j.val → Fin u → F)),
        μ.real ({ω | (ι ω, fun t : Fin j.val => R (ι ω (Fin.castLE j.isLt.le t)) ω) ∈ S} ∩
            {ω | R (ι ω j) ω ∈ Submodule.span F
              (Set.range fun t : Fin j.val => R (ι ω (Fin.castLE j.isLt.le t)) ω)}) ≤
          (q : ℝ) ^ j.val * ρ j.val *
            μ.real {ω | (ι ω, fun t : Fin j.val => R (ι ω (Fin.castLE j.isLt.le t)) ω) ∈ S})
    (a : ℕ) (ha1 : 1 ≤ a) (ham : a ≤ m) (hk1 : 1 ≤ k) (hka : k ≤ a)
    (y : Fin ℓ → F) :
    μ.real {ω | a ≤ (Finset.univ.filter
        (fun i => (fun c => ∑ d, Z ω c d * R i ω d) = y)).card} ≤
      ((m.choose k : ℝ) / (a.choose k : ℝ)) * (1 / ((q : ℝ) ^ ℓ) ^ k) *
        ∏ j ∈ Finset.Ico 1 k, (1 + ((q : ℝ) ^ ℓ - 1) * (q : ℝ) ^ j * ρ j) ∧
    μ.real {ω | a ≤ Finset.univ.sup (fun y' : Fin ℓ → F => (Finset.univ.filter
        (fun i => (fun c => ∑ d, Z ω c d * R i ω d) = y')).card)} ≤
      ((m.choose k : ℝ) / (a.choose k : ℝ)) * (1 / ((q : ℝ) ^ ℓ) ^ (k - 1)) *
        ∏ j ∈ Finset.Ico 1 k, (1 + ((q : ℝ) ^ ℓ - 1) * (q : ℝ) ^ j * ρ j) := by sorry

end ProdMomentConc.Supplement
