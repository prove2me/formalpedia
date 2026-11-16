-- Prove2me | Theorems.Thm_PrivPCP_Supplement_theorem_4_12
-- name    : PrivPCP.Supplement.theorem_4_12
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T23:57:31.898273+00:00
-- url     : https://prove2.me/theorems/ecd138cc-8a53-4dda-9a48-a038c9bb8a86
-- title:
--   Theorem 4.12 — specialized Corvaja–Zannier estimate $\Gamma_F\le\max\{3\sqrt[3]{2}(2Na^2b^2)^{1/3},12Nab/q\}\le C(N^{1/3}(ab)^{2/3}+ab)$
-- statement:
--   Let $q$ be prime and $\mathbb K=\overline{\mathbb F}_q$. Let $F\in\mathbb K[X,Y]$ be irreducible of bidegree $(a,b)=(\deg_XF,\deg_YF)$ with $a,b>0$, let $\mathcal X_F$ be the normalization of the closure of $\{F=0\}$ in $\mathbb P^1\times\mathbb P^1$, and let $x,y\in\mathbb K(\mathcal X_F)$ be its coordinate functions. Let $n_1,n_2$ be positive integers and $N=n_1n_2$. Suppose that
--   1. $N<q$;
--   2. $x^{n_1}$ and $y^{n_2}$ are **multiplicatively independent modulo constants**: $(x^{n_1})^r(y^{n_2})^s\in\mathbb K^\times$ with $r,s\in\mathbb Z$ only for $r=s=0$;
--   3. $d(x^{n_1})\ne0$ and $d(y^{n_2})\ne0$.
--
--   Then $\Gamma_F$, the weighted common-zero count of eq. (18), is finite, and there is an absolute constant $C$ with
--   $$
--   \Gamma_F\le\max\Bigl\{3\sqrt[3]{2}\,\bigl(2Na^2b^2\bigr)^{1/3},\ \frac{12Nab}{q}\Bigr\}\le C\bigl(N^{1/3}(ab)^{2/3}+ab\bigr).
--   $$
--
--   This is the specialization of the Corvaja–Zannier gcd estimate that the proof of the coprime-subgroup divisibility lemma (Lemma 4.13), and through it two-dimensional product expansion (Theorem 4.11), relies on: it bounds how many points of the subgroup grid $\{\alpha^{n_1}=\beta^{n_2}=1\}$ an irreducible curve of small bidegree can pass through, counted with branch multiplicity.
--
--   **Formalization Note** The function field $\mathbb K(\mathcal X_F)$ with its coordinate functions is any field $L\supseteq\mathbb K$ with $x,y\in L$ such that the kernel of $\mathbb K[X,Y]\to L$, $X\mapsto x$, $Y\mapsto y$, is $(F)$ and $L=\mathbb K(x,y)$; this pins $(L,x,y)$ down up to isomorphism as $\operatorname{Frac}(\mathbb K[X,Y]/(F))$. The points of $\mathcal X_F$ are the places of $L/\mathbb K$, and $d$ is the Kähler differential $\Omega_{L/\mathbb K}$. The constant $C$ is chosen before $q$, $F$, $n_1$, $n_2$. Cube roots are real powers $t^{1/3}$.
--
--   Differences from the source:
--   - encoding: the points $\nu$ of the normalization $\mathcal X_F$ → the places of $L/\mathbb K$ (published `AlgebraicCurve.Place`) with normalized order $\operatorname{ord}_\nu$, and $x(\nu),y(\nu)\in\mathbb K^\times$ as $\operatorname{ord}_\nu x=\operatorname{ord}_\nu y=0$; reason: over the algebraically closed $\mathbb K$ the points of the smooth projective model are exactly the places of its function field.
--   - encoding: $\mathbb K(\mathcal X_F)$ with coordinate functions $x,y$ → any field $L$ with $x,y\in L$, $\ker(\mathbb K[X,Y]\to L)=(F)$ and $L=\mathbb K(x,y)$; reason: these conditions determine $(L,x,y)$ up to isomorphism as $\operatorname{Frac}(\mathbb K[X,Y]/(F))$.
--   - encoding: the formal differential $du$ → the Kähler differential $d u\in\Omega_{L/\mathbb K}$; reason: the same differential.
--   - encoding: $\Gamma_F$ as a number → a sum in $\mathbb N\cup\{\infty\}$, with its finiteness stated as part of the conclusion; reason: the source's inequality bounds $\Gamma_F$ by a real number, so it is finite there too.
--   - encoding: "for an absolute constant $C$" → $\exists C$ quantified before $q,F,a,b,n_1,n_2$; reason: this is what absolute means.
-- source:
--   Bafna, Vyas, Private PCPs from Product Expansion, STOC 2027 submission manuscript (sha256 c2cac1e07fc4af8721f673867373fc5bd417aa65f45cf170c543568abcf1e47e), Theorem 4.12, p.23 (PDF p.25), with the set-up of §4.4.1, pp.22–23 (PDF pp.24–25)

import Mathlib
import Definitions.Def_PrivPCP_Supplement_gammaF

set_option autoImplicit false

namespace PrivPCP.Supplement

/-- **Theorem 4.12 (Specialized Corvaja–Zannier estimate)** (Bafna, Vyas, *Private PCPs from Product
Expansion*, STOC 2027 submission manuscript (sha256 c2cac1e0…), Theorem 4.12, p.23, with the set-up of
§4.4.1, pp.22–23). Let `q` be prime and `𝕂 = 𝔽̄_q`. Let `F ∈ 𝕂[X, Y]` be irreducible of bidegree
`(a, b)`, `a, b > 0`, and let `x, y` be the coordinate functions on `𝒳_F`. Let `n₁, n₂` be positive
integers and `N = n₁n₂`. Suppose `N < q`, that `x^{n₁}` and `y^{n₂}` are multiplicatively independent
modulo constants (`u^r v^s ∈ 𝕂^×` with `r, s ∈ ℤ` only for `r = s = 0`), and that `d(x^{n₁}) ≠ 0`,
`d(y^{n₂}) ≠ 0`. Then, for an absolute constant `C`,
`Γ_F ⩽ max{3·∛2·(2Na²b²)^{1/3}, 12Nab/q} ⩽ C(N^{1/3}(ab)^{2/3} + ab)`.

**Formalization Note** The function field `𝕂(𝒳_F)` with its coordinate functions is any field `L ⊇ 𝕂`
with `x, y ∈ L` such that the kernel of `𝕂[X, Y] → L`, `X ↦ x`, `Y ↦ y`, is `(F)` and `L` is generated
as a field by `x, y` over `𝕂`; this determines `(L, x, y)` up to isomorphism as
`Frac(𝕂[X, Y]/(F))`. The bidegree is `(deg_X F, deg_Y F)`; `d` is the Kähler differential
`Ω[L⁄𝕂]`. `Γ_F` is `gammaF` (eq. (18)), a sum in `ℕ∞`; the first inequality includes that it is
finite. `C` is fixed before `q`, `F`, `n₁`, `n₂`. -/
theorem theorem_4_12 : ∃ C : ℝ, ∀ (q : ℕ) [Fact q.Prime]
    (F : MvPolynomial (Fin 2) (AlgebraicClosure (ZMod q))) (a b : ℕ),
    Irreducible F → F.degreeOf 0 = a → F.degreeOf 1 = b → 0 < a → 0 < b →
    ∀ (L : Type) [Field L] [Algebra (AlgebraicClosure (ZMod q)) L] (x y : L),
    RingHom.ker (MvPolynomial.aeval (R := AlgebraicClosure (ZMod q)) ![x, y]).toRingHom =
      Ideal.span {F} →
    IntermediateField.adjoin (AlgebraicClosure (ZMod q)) {x, y} = ⊤ →
    ∀ n₁ n₂ : ℕ, 0 < n₁ → 0 < n₂ → n₁ * n₂ < q →
    (∀ r s : ℤ, (∃ c : AlgebraicClosure (ZMod q), c ≠ 0 ∧
      (x ^ n₁) ^ r * (y ^ n₂) ^ s = algebraMap (AlgebraicClosure (ZMod q)) L c) → r = 0 ∧ s = 0) →
    KaehlerDifferential.D (AlgebraicClosure (ZMod q)) L (x ^ n₁) ≠ 0 →
    KaehlerDifferential.D (AlgebraicClosure (ZMod q)) L (y ^ n₂) ≠ 0 →
    gammaF (AlgebraicClosure (ZMod q)) L x y n₁ n₂ ≠ ⊤ ∧
    ((gammaF (AlgebraicClosure (ZMod q)) L x y n₁ n₂).toNat : ℝ) ≤
      max (3 * (2 : ℝ) ^ ((1 : ℝ) / 3) *
            (2 * ((n₁ * n₂ : ℕ) : ℝ) * (a : ℝ) ^ 2 * (b : ℝ) ^ 2) ^ ((1 : ℝ) / 3))
          (12 * ((n₁ * n₂ : ℕ) : ℝ) * a * b / q) ∧
    max (3 * (2 : ℝ) ^ ((1 : ℝ) / 3) *
            (2 * ((n₁ * n₂ : ℕ) : ℝ) * (a : ℝ) ^ 2 * (b : ℝ) ^ 2) ^ ((1 : ℝ) / 3))
          (12 * ((n₁ * n₂ : ℕ) : ℝ) * a * b / q) ≤
      C * (((n₁ * n₂ : ℕ) : ℝ) ^ ((1 : ℝ) / 3) * ((a : ℝ) * b) ^ ((2 : ℝ) / 3) + (a : ℝ) * b) := by sorry

end PrivPCP.Supplement
