-- Prove2me | Theorems.Thm_StabGen_Entropy_lemma21
-- name    : StabGen.Entropy.lemma21
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T17:12:47.47873+00:00
-- url     : https://prove2.me/theorems/f6fa8af8-031a-4bab-b492-e4dd3416a4b8
-- title:
--   Lemma 21 — Bregman divergences of the regularizer between the minimizers of (19) and (20)
-- statement:
--   Let $E$ be a real normed vector space whose elements $g$ act as functions $x\mapsto g(x)$ on $X$ through a linear map, and let $\ell(g,z)=c(g(x),y)$ be $\sigma$-admissible with respect to $E$ (Definition 19). Let $N:E\to\mathbb R$ be convex, let $\lambda>0$, and assume that $N$ and every $g\mapsto\ell(g,z)$ are differentiable. Fix a training set $S=(z_1,\dots,z_m)$ with $z_j=(x_j,y_j)$ and an index $i$. If $f$ minimizes $R_r$ in (19) over $E$ and $f^{\setminus i}$ minimizes $R_r^{\setminus i}$ in (20) over $E$, then, with $\Delta f=f^{\setminus i}-f$,
--   $$d_N(f,f^{\setminus i})+d_N(f^{\setminus i},f)\le\frac1{\lambda m}\Bigl(\ell(f^{\setminus i},z_i)-\ell(f,z_i)-d_{\ell(\cdot,z_i)}(f^{\setminus i},f)\Bigr)\le\frac{\sigma}{\lambda m}|\Delta f(x_i)| ,$$
--   where $d$ denotes the Bregman divergence.
--
--   Lemma 21 is the general tool behind the stability bounds for regularized algorithms: it turns optimality of the two minimizers into a bound on the symmetrized divergence of the regularizer.
--
--   **Formalization Note** This is the differentiable case, the case the lemma states ("when $N$ and $\ell$ are differentiable"). A differentiable convex $N:E\to\mathbb R$ is automatically proper and closed. The minimizers are assumed for the given $S$ and $i$ only. The proof of Theorem 24 applies Lemma 21 to $N=K(\cdot,f_0)$ on the convex set of densities, which is not a vector space and on which $K(\cdot,f_0)$ is not differentiable everywhere; the goal theorem of this mission does not instantiate the statement below, and its truth does not depend on it.
-- source:
--   Bousquet & Elisseeff, Stability and Generalization, JMLR 2 (2002), p. 513, Lemma 21 (conditions of Lemma 20, pp. 512–513; Definition 19, p. 512; Bregman divergence, Appendix C, p. 525)

import Mathlib
import Definitions.Def_StabGen_Entropy_GeneralRegularization

namespace StabGen.Entropy

open FoundationsML.Stability

/-- Lemma 21, p. 513, differentiable case: `F` is a real normed vector space `E` whose elements
are functions on `X` through the linear map `ev`; the loss `ℓ(g, z) = c(g(x), y)` is
`σ`-admissible; `N : E → ℝ` is convex; `N` and `ℓ(·, z)` are differentiable; `f` minimizes (19)
and `f'` (the paper's `f^{\i}`) minimizes (20). Then
`d_N(f, f') + d_N(f', f) ≤ (1/(λm)) (ℓ(f', z_i) − ℓ(f, z_i) − d_{ℓ(·, z_i)}(f', f))
  ≤ (σ/(λm)) |Δf(x_i)|`, with `Δf = f' − f`. -/
theorem lemma21 {X Y E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {m : ℕ}
    (ev : E →ₗ[ℝ] (X → ℝ)) (c : ℝ → Y → ℝ) (σ lam : ℝ) (N : E → ℝ)
    (S : Fin m → X × Y) (i : Fin m) (f f' : E)
    (hσ : StabGen.RKHS.SigmaAdmissible (Set.range ev) c σ) (hlam : 0 < lam)
    (hN : ConvexOn ℝ Set.univ N) (hNd : Differentiable ℝ N)
    (hℓd : ∀ z : X × Y, Differentiable ℝ (fun g : E => Loss c (ev g) z))
    (hmin : ∀ g : E, StabGen.RKHS.regRisk c ev S lam N f ≤ StabGen.RKHS.regRisk c ev S lam N g)
    (hmin' : ∀ g : E, StabGen.RKHS.truncRegRisk c ev S i lam N f' ≤ StabGen.RKHS.truncRegRisk c ev S i lam N g) :
    bregmanDiv N f f' + bregmanDiv N f' f ≤
        (1 / (lam * (m : ℝ))) *
          (Loss c (ev f') (S i) - Loss c (ev f) (S i) -
            bregmanDiv (fun g : E => Loss c (ev g) (S i)) f' f) ∧
      (1 / (lam * (m : ℝ))) *
          (Loss c (ev f') (S i) - Loss c (ev f) (S i) -
            bregmanDiv (fun g : E => Loss c (ev g) (S i)) f' f) ≤
        (σ / (lam * (m : ℝ))) * |ev (f' - f) (S i).1| := by sorry

end StabGen.Entropy
