-- Prove2me | Theorems.Thm_TrDegJac_lemma_4_11
-- name    : TrDegJac.lemma_4_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:37:14.603532+00:00
-- url     : https://prove2.me/theorems/9b45b5b2-374f-4782-8c3f-19640f52d1e3
-- title:
--   Lemma 4.11 — a greedy ordering with $[K_{k-1}(x):K_{k-1}]\le[\mathbb F(x):\mathbb F(f)]^{1/k}$
-- statement:
--   Let $f_1,\dots,f_n\in\mathbb F[x_1,\dots,x_n]$ be algebraically independent over $\mathbb F$. Then there is an ordering $x_{i_1},\dots,x_{i_n}$ of the variables such that, writing $K_k=\mathbb F(f,x_{i_1},\dots,x_{i_k})$ (so $K_0=\mathbb F(f)$), for every $k\in\{1,\dots,n\}$ and every variable $x\in\{x_1,\dots,x_n\}$,
--   $$
--   [K_{k-1}(x):K_{k-1}]\ \le\ [\mathbb F(x):\mathbb F(f)]^{1/k},
--   \qquad\text{equivalently}\qquad [K_{k-1}(x):K_{k-1}]^k\le[\mathbb F(x):\mathbb F(f)].
--   $$
--
--   After adjoining the first $k-1$ chosen variables, every remaining variable has small degree; with $k=\lfloor\log_p D\rfloor+1$ this degree is below $p$, which is how Theorem 4.12 obtains separability.
--
--   **Formalization Note** The ordering is a permutation $\sigma$ of $\{0,\dots,n-1\}$ with $x_{i_\ell}=x_{\sigma(\ell-1)}$; $K_{k-1}$ is generated over $\mathbb F$ by $f$ and the $x_{\sigma(\ell)}$ with $\ell+1<k$.
--
--   Differences from the source:
--   - encoding: an ordering x_{i_1}, …, x_{i_n} with K_k := F(f, x_{i_1}, …, x_{i_k}) → a permutation σ of Fin n, with K_{k−1} adjoining X (σ ℓ) for ℓ + 1 < k; reason: 0-based indices; x_{i_ℓ} = X (σ (ℓ − 1))
--   - encoding: [K_{k−1}(x) : K_{k−1}] ≤ [F(x) : F(f)]^{1/k} → (Module.rank K_{k−1} K_{k−1}(x))^k ≤ Module.rank F(f) F(x), in cardinals; reason: for real a, D ≥ 0 and k ≥ 1, a ≤ D^{1/k} iff a^k ≤ D; D is finite by Proposition 3.30 and a^k ≤ D forces a finite
-- source:
--   Forbes and Staicu, Approximating Transcendence Degree in Medium Characteristic, STOC 2027 submission (manuscript sha256 3ab72a42…), Lemma 4.11, p.28

import Mathlib
import Definitions.Def_TrDegJac_RatFn
import Definitions.Def_TrDegJac_adjoinFamily

set_option autoImplicit false

namespace TrDegJac

/-- **Lemma 4.11 (greedy ordering of the variables)** — Forbes and Staicu, *Approximating Transcendence Degree in Medium Characteristic*, STOC 2027
submission (manuscript sha256 3ab72a42…), p.28:
"For any f₁, …, f_n ∈ F[x₁, …, x_n] algebraically independent, there exists an ordering
x_{i₁}, …, x_{i_n} of x such that for all k ∈ [n] and any x ∈ x, writing
K_k := F(f, x_{i₁}, …, x_{i_k}), [K_{k−1}(x) : K_{k−1}] ≤ [F(x) : F(f)]^{1/k}."

**Formalization Note.** The ordering is a permutation `σ` of `Fin n` with `x_{i_ℓ} = X (σ (ℓ − 1))`
(0-based), so `K_{k−1}` adjoins to `F(f)` the variables `X (σ ℓ)` with `ℓ + 1 < k`, i.e. the first
`k − 1` chosen variables; `K₀ = F(f)`. `K_{k−1}(x)` is `IntermediateField.adjoin K_{k−1} {x}`. Degrees
are `Module.rank` (cardinals). The bound `a ≤ D^{1/k}` is written `a^k ≤ D`, equivalent for real
`a, D ≥ 0` and `k ≥ 1`; `D = [F(x) : F(f)]` is finite by Proposition 3.30, and `a^k ≤ D` then forces
`a` to be finite too. -/
theorem lemma_4_11 {F : Type*} [Field F] {n : ℕ} (f : Fin n → MvPolynomial (Fin n) F)
    (hf : AlgebraicIndependent F f) :
    ∃ σ : Equiv.Perm (Fin n), ∀ k : ℕ, 1 ≤ k → k ≤ n → ∀ j : Fin n,
      let K : IntermediateField F (RatFn F n) :=
        IntermediateField.adjoin F
          (Set.range (fun i => toRatFn (f i)) ∪
            {y | ∃ ℓ : Fin n, ℓ.val + 1 < k ∧ y = toRatFn (MvPolynomial.X (σ ℓ) : MvPolynomial (Fin n) F)})
      Module.rank K (IntermediateField.adjoin K {toRatFn (MvPolynomial.X j : MvPolynomial (Fin n) F)}) ^ k ≤
        Module.rank (adjoinFamily f) (RatFn F n) := by sorry

end TrDegJac
