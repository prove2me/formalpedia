-- Prove2me | Theorems.Thm_QAlgorithms_Papers_DQI24_dqi_semicircle_law
-- name    : QAlgorithms.Papers.DQI24.dqi_semicircle_law
-- status  : Open
-- author  : @Goku
-- created : 2026-10-18T19:06:24.676272+00:00
-- url     : https://prove2.me/theorems/b8e2bc33-a7cd-4899-bc0f-d8e6b4f948e3
-- title:
--   DQI semicircle law: optimal expected fraction of satisfied max-LINSAT constraints under perfect decoding
-- statement:
--   This is the semicircle law of decoded quantum interferometry (DQI) with perfect decoding.
--
--   Let $p$ be a prime and $r\in\{1,\dots,p-1\}$. A max-LINSAT instance consists of a matrix $B\in\mathbb F_p^{m\times n}$ with rows $b_1,\dots,b_m$ and subsets $F_1,\dots,F_m\subseteq\mathbb F_p$; constraint $i$ is $b_i\cdot x\in F_i$ for $x\in\mathbb F_p^n$. Put $f_i=+1$ on $F_i$ and $-1$ off it, and $f(x)=\sum_i f_i(b_i\cdot x)$. For a polynomial $P$ with complex coefficients the DQI state is $|P(f)\rangle=\sum_{x\in\mathbb F_p^n}P(f(x))\,|x\rangle$. Let $\langle s\rangle_{\mathrm{opt}}(\ell)$ be the supremum, over all $P$ of degree at most $\ell$ with $\||P(f)\rangle\|=1$, of the expected number of satisfied constraints when $|P(f)\rangle$ is measured in the computational basis (outcome $x$ with probability $|P(f(x))|^2$). Let $d^\perp$ be the minimum Hamming weight of a nonzero codeword of $C^\perp=\{d\in\mathbb F_p^m: B^{\mathsf T}d=0\}$.
--
--   Fix $\mu\ge 0$ and write $\rho=r/p$. Consider instances with $|F_i|=r$ for all $i$, $m>n$, $\ell=\mu m$ and $2\ell+1<d^\perp$. Then, as $m\to\infty$,
--
--   $$
--   \frac{\langle s\rangle_{\mathrm{opt}}(\ell)}{m}\;\longrightarrow\;\begin{cases}\left(\sqrt{\mu(1-\rho)}+\sqrt{\rho(1-\mu)}\right)^2 & \text{if } \rho\le 1-\mu,\\ 1 & \text{otherwise,}\end{cases}
--   $$
--
--   uniformly over such instances: for every $\varepsilon>0$ there is $M$ such that every such instance with $m\ge M$ has $\langle s\rangle_{\mathrm{opt}}(\ell)/m$ within $\varepsilon$ of the right-hand side.
--
--   The theorem converts any decoding guarantee for the code $C^\perp$ out to $\ell$ errors into an approximation guarantee for max-LINSAT, and it is the basis of the paper's comparison of DQI with classical optimizers (e.g. on Optimal Polynomial Intersection).
--
--   **Formalization Note** The source's limit over an arbitrary sequence of instances is stated in the equivalent uniform $\varepsilon$–$M$ form, with $M$ chosen after $p,r,\mu,\varepsilon$ and before the instance. The hypothesis $m>n$ is taken from Lemma 9.2, on which the source's proof of the theorem rests. The optimum is over polynomials of degree at most $\ell$ (as in the proof, which optimizes over all unit coefficient vectors $w\in\mathbb C^{\ell+1}$); $\ell=\mu m$ is required exactly, so values of $\mu$ for which $\mu m$ is never an integer make the statement vacuous, as in the source.
-- source:
--   Optimization by Decoded Quantum Interferometry (Jordan, Shutty, Wootters, Zalcman, Schmidhuber, King, Isakov, Khattar, Babbush), arXiv:2408.08292v5, Theorem 4.1, PDF p. 11. https://arxiv.org/abs/2408.08292v5 . PDF SHA-256: 6357170bb5566b483f72cc95316490cbc7ea8b81678279f3c0836df3929a1b62.

import Definitions.Def_QAlgorithms_Defs_DQI
set_option autoImplicit false

namespace QAlgorithms.Papers.DQI24

open QAlgorithms

/-- DQI Theorem 4.1 (p.11; proof §9.4, p.34): let `p` be prime and `r ∈ {1, …, p − 1}`, and fix
`μ = ℓ/m`. For max-LINSAT instances `B ∈ F_p^{m×n}`, `F_1, …, F_m ⊆ F_p` with `|F_i| = r` for
all `i`, `m > n` (Lemma 9.2, p.26, on which the proof rests), and
`2ℓ + 1 < d⊥` (every nonzero `d ∈ F_p^m` with `Bᵀ d = 0` has Hamming weight `> 2ℓ + 1`), the
optimal expected number `⟨s⟩_opt` of satisfied constraints over unit-norm DQI states `|P(f)⟩` with
`deg P ≤ ℓ` satisfies, in the limit `m → ∞` with `ℓ/m = μ` fixed,
`⟨s⟩_opt / m → (√(μ(1 − r/p)) + √((r/p)(1 − μ)))²` if `r/p ≤ 1 − μ`, and `→ 1` otherwise.
The limit is stated uniformly: for every `ε > 0` there is `M` such that every such instance
with `m ≥ M` is within `ε` of the limit value. -/
theorem dqi_semicircle_law (p : ℕ) [Fact p.Prime] (r : ℕ) (hr1 : 1 ≤ r) (hr2 : r < p) (μ : ℝ) :
    ∀ ε : ℝ, 0 < ε → ∃ M : ℕ, ∀ (m n : ℕ) (B : Matrix (Fin m) (Fin n) (ZMod p))
      (F : Fin m → Finset (ZMod p)) (ℓ : ℕ),
      M ≤ m → n < m → (ℓ : ℝ) = μ * m → (∀ i, (F i).card = r) →
      DualDistanceExceeds B (2 * ℓ + 1) →
      |dqiOptimalSatisfied B F ℓ / m - semicircleValue μ ((r : ℝ) / p)| ≤ ε := by
  sorry

end QAlgorithms.Papers.DQI24
