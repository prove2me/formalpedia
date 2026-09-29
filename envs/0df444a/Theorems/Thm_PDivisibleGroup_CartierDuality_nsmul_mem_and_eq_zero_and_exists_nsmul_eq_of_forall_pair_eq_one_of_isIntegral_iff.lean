-- Prove2me | Theorems.Thm_PDivisibleGroup_CartierDuality_nsmul_mem_and_eq_zero_and_exists_nsmul_eq_of_forall_pair_eq_one_of_isIntegral_iff
-- name    : PDivisibleGroup.CartierDuality.nsmul_mem_and_eq_zero_and_exists_nsmul_eq_of_forall_pair_eq_one_of_isIntegral_iff
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:58.387243+00:00
-- url     : https://prove2.me/theorems/89b2d859-8fb7-547b-8846-bd5ec8fc9e9c
-- title:
--   Tate's pairing kernel: torsion-free and p-divisible part
-- statement:
--   Fix a prime $p$ and write $\overline{\mathbb Q}_p$ for `PadicAlgCl p`. Let $R$ be a commutative ring with an algebra map to $\overline{\mathbb Q}_p$ such that an element $x\in\overline{\mathbb Q}_p$ is integral over $R$ exactly when $\|x\|\le 1$, and put $\mathcal O=$ `integralClosure R (PadicAlgCl p)`. Let $G,G'$ be $p$-divisible groups of height $h$ over $R$ (finite free cocommutative Hopf algebras `level v` of rank $p^{vh}$, with surjective transitions whose kernels are the $p^v$-torsion ideals) and let $D$ be a Cartier duality between them, i.e. isomorphisms $G'.\mathrm{level}\,v\cong \mathrm{CartierDual}(G.\mathrm{level}\,v)$ compatible with transition and multiplication by $p$; `D.pair L w` denotes the resulting pairing $\sum_i f(b_i)\,\psi(b^i)$ on points with values in an $R$-algebra $L$. Three subsets $\mathrm{Ker}$, $G_1$, $\mathrm{Inv}$ of the completed points $G.\mathrm{CPoints}\,\mathcal O$ (compatible families of points over the rings $\mathcal O/p^i$) are given, characterised by hypotheses as follows. $Y\in\mathrm{Ker}$ iff for every element $y$ of the Tate module of $G'(\overline{\mathbb Q}_p)$ (sequences with $p^n y_n=0$, $p\,y_{n+1}=y_n$), all $i\le w$, every $f\in G.\mathrm{Point}(\mathcal O/p^i, w)$ whose class in $G.\mathrm{Points}(\mathcal O/p^i)$ is the $i$-th component of $Y$, and every $\psi\in G'.\mathrm{Point}(\mathcal O,w)$ whose class in $G'.\mathrm{Points}(\overline{\mathbb Q}_p)$ is $y_w$, one has $D.\mathrm{pair}$ of $f$ against the reduction of $\psi$ mod $p^i$ equal to $1$. $X\in G_1$ iff for every $w$, every $f\in G.\mathrm{Point}(\mathcal O/p^{1},w)$ representing the first component of $X$ and every $a\in G.\mathrm{level}\,w$, the element $f(a)-\varepsilon(a)$ is nilpotent. $X\in\mathrm{Inv}$ iff $\sigma'\cdot X=X$ for every $\mathbb Q_p$-algebra automorphism $\sigma$ of $\overline{\mathbb Q}_p$ and every $R$-algebra automorphism $\sigma'$ of $\mathcal O$ inducing $\sigma$. The conclusion asserts three things: $\mathrm{Ker}$ is stable under multiplication by every natural number $n$; if $Y\in\mathrm{Ker}$ and $p^kY=0$ then $Y=0$; and for $X$ lying in $\mathrm{Ker}\cap G_1\cap\mathrm{Inv}$ there is $X_1$ again in $\mathrm{Ker}\cap G_1\cap\mathrm{Inv}$ with $pX_1=X$.
--
--   This is the content of Steps 1 and 2 of Tate's Proposition 11 on $p$-divisible groups — the kernel of the map $\alpha$ from completed points to $\mathrm{Hom}(T(G'),U)$ is uniquely $p$-divisible — arranged so that the $p$-th roots produced stay inside the formal part and are Galois-invariant, without recourse to the connected–étale sequence. It feeds the injectivity statement [`PDivisibleGroup.CartierDuality.cpoints_eq_zero_of_forall_pair_eq_one_of_forall_mem_range_iff`](thm.html#PDivisibleGroup.CartierDuality.cpoints_eq_zero_of_forall_pair_eq_one_of_forall_mem_range_iff) for integral points.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_PDivisibleGroup_CartierDuality_nsmul_mem_and_eq_zero_and_exists_nsmul_eq_of_forall_pair_eq_one_of_isIntegral_iff.lean

import Mathlib
import Definitions.Def_PDivisibleGroup_CartierDuality
import Definitions.Def_PDivisibleGroup_CompletedPoints

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem PDivisibleGroup.CartierDuality.nsmul_mem_and_eq_zero_and_exists_nsmul_eq_of_forall_pair_eq_one_of_isIntegral_iff
    (p : ℕ) [Fact p.Prime] {R : Type} [CommRing R] [Algebra R (PadicAlgCl p)]
    (hO : ∀ x : PadicAlgCl p, IsIntegral R x ↔ ‖x‖ ≤ 1)
    {h : ℕ} {G G' : PDivisibleGroup R p h} (D : G.CartierDuality G')
    (Ker G₁ Inv : Set (G.CPoints (integralClosure R (PadicAlgCl p))))
    (hKer : ∀ Y, Y ∈ Ker ↔
      ∀ (y : TateModule p (G'.Points (PadicAlgCl p))) (i w : ℕ), i ≤ w →
        ∀ (f : G.Point (integralClosure R (PadicAlgCl p) ⧸
            Ideal.span {(p : integralClosure R (PadicAlgCl p)) ^ i}) w),
          G.pointsMkAdd _ w (Additive.ofMul f) = G.cpointsProj (integralClosure R (PadicAlgCl p)) i Y →
        ∀ (ψ : G'.Point (integralClosure R (PadicAlgCl p)) w),
          G'.pointsMkAdd (PadicAlgCl p) w
              (Additive.ofMul (G'.pointMap (integralClosure R (PadicAlgCl p)).val w ψ)) =
            (y : ℕ → G'.Points (PadicAlgCl p)) w →
          D.pair _ w f (G'.pointMap (Ideal.Quotient.mkₐ R
              (Ideal.span {(p : integralClosure R (PadicAlgCl p)) ^ i})) w ψ) = 1)
    (hG₁ : ∀ X, X ∈ G₁ ↔
      ∀ (w : ℕ) (f : G.Point (integralClosure R (PadicAlgCl p) ⧸
          Ideal.span {(p : integralClosure R (PadicAlgCl p)) ^ 1}) w),
        G.pointsMkAdd _ w (Additive.ofMul f) = G.cpointsProj (integralClosure R (PadicAlgCl p)) 1 X →
        ∀ a : G.level w,
          IsNilpotent (PDivisibleGroup.Point.toAlgHom f a - algebraMap R _ (Coalgebra.counit a)))
    (hInv : ∀ X, X ∈ Inv ↔
      ∀ (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)
        (σ' : integralClosure R (PadicAlgCl p) ≃ₐ[R] integralClosure R (PadicAlgCl p)),
        (∀ a : integralClosure R (PadicAlgCl p),
            ((σ' a : integralClosure R (PadicAlgCl p)) : PadicAlgCl p) = σ a) →
        σ' • X = X) :
    (∀ Y ∈ Ker, ∀ n : ℕ, n • Y ∈ Ker) ∧
    (∀ Y ∈ Ker, ∀ k : ℕ, p ^ k • Y = 0 → Y = 0) ∧
    (∀ X ∈ Ker, X ∈ G₁ → X ∈ Inv → ∃ X₁ ∈ Ker, X₁ ∈ G₁ ∧ X₁ ∈ Inv ∧ p • X₁ = X) := by sorry
