-- Prove2me | Theorems.Thm_SilverRateSC_lemma_A_3
-- name    : SilverRateSC.lemma_A_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T03:45:57.853914+00:00
-- url     : https://prove2.me/theorems/f688923e-8f46-4e07-9825-86158fe86a40
-- title:
--   Lemma A.3 — projection properties of $\mathrm{env}_1\sigma_K((X,Y)-z^\circ)$
-- statement:
--   Let $K\subset\mathbb R^2$ be compact and convex with $0\in K$, and let $z^\circ=(z_1,z_2)\in\mathbb R^2$. The function
--   $$\Phi(X,Y)=(\mathrm{env}_1\sigma_K)\bigl((X,Y)-z^\circ\bigr)=\max_{g\in K}\Bigl\{\langle g,(X,Y)-z^\circ\rangle-\tfrac12\|g\|^2\Bigr\}$$
--   (where $(\mathrm{env}_1\sigma_K)(x)=\min_y\{\sigma_K(y)+\frac12\|x-y\|^2\}$) is nonnegative, convex and $1$-smooth, with $\nabla\Phi(X,Y)=\Pi_K((X,Y)-z^\circ)$. Suppose $K\subset\{(p,-q):p,q\ge0\}$. Then:
--   1. $\partial_Y\Phi(X,Y)\le0$ for all $(X,Y)$;
--   2. if, for some $\theta>0$ and $\ell_i\ge0$, every $(p,-q)\in K$ satisfies $q\le p/\theta$, and $z_2\ge0$, $z_1\ge\ell_i+z_2/\theta$, then $\Phi(X,Y)=0$ whenever $X\le\ell_i$, $Y\ge0$;
--   3. if $(p,0)\in K$ whenever $(p,-q)\in K$, then $\partial_Y\Phi(X,Y)=0$ whenever $Y\ge z_2$.
--
--   These are the sufficient conditions used to verify the zero sets and sign properties of the bending and bridging components.
--
--   Differences from the source:
--   - encoding: (env_1 σ_K)(x) = min_y {σ_K(y) + ½‖x − y‖²} = max_{g∈K} {…} → Φ z := envSupp K (z − z°) (the max form), with clauses IsLeast {σ_K(y) + ½‖(z − z°) − y‖²} (Φ z) in EReal, using DualRCD.suppFn, and IsGreatest of the max form; reason: both displayed forms of Φ are asserted
--   - encoding: functions on ℝ², ∂_Y, 1-smooth, Π_K → EuclideanSpace ℝ (Fin 2), coordinate 1 of gradient, KatyushaNs.IsConvexLSmooth 1, OrabonaOL.OGD.IsEuclideanProj; reason: Lean representation; same objects
--   - encoding: K ⊂ {(p,−q) : p, q ≥ 0}; (p,−q) ∈ K; z° = (z_1, z_2) → ∀ g ∈ K, 0 ≤ g 0 ∧ g 1 ≤ 0; g = (g 0, g 1); z_1 = z° 0, z_2 = z° 1; reason: same sets and coordinates
-- source:
--   Liu, Ye, Silver Rate Is (Almost) Optimal for Gradient Descent: The Strongly Convex Case, arXiv:2609.26873 (sha256 1e325f28…), Lemma A.3, p.37; Fact A.1, p.29

import Mathlib
import Definitions.Def_SilverRateSC_envSupp
import Definitions.Def_KatyushaNs_IsConvexLSmooth
import Definitions.Def_OrabonaOL_OGD_IsEuclideanProj
import Definitions.Def_DualRCD_suppFn

open scoped InnerProductSpace

namespace SilverRateSC

/-- **Lemma A.3 (Projection properties).** Let `K ⊂ ℝ²` be compact and convex, with `0 ∈ K`, and
let `z° = (z_1, z_2) ∈ ℝ²`. The function
`Φ(X, Y) = (env₁ σ_K)((X, Y) − z°) = max_{g ∈ K} {⟨g, (X, Y) − z°⟩ − ½‖g‖²}` is nonnegative,
convex and `1`-smooth, with `∇Φ(X, Y) = Π_K((X, Y) − z°)`. Suppose `K ⊂ {(p, −q) : p, q ≥ 0}`.
Then (i) `∂_YΦ ≤ 0` everywhere; (ii) if, for some `θ > 0` and `ℓ_i ≥ 0`, every `(p, −q) ∈ K`
satisfies `q ≤ p/θ`, and `z_2 ≥ 0`, `z_1 ≥ ℓ_i + z_2/θ`, then `Φ(X, Y) = 0` whenever `X ≤ ℓ_i`,
`Y ≥ 0`; (iii) if `(p, 0) ∈ K` whenever `(p, −q) ∈ K`, then `∂_YΦ(X, Y) = 0` whenever `Y ≥ z_2`.

Liu, Ye, *Silver Rate Is (Almost) Optimal for Gradient Descent: The Strongly Convex Case*,
arXiv:2609.26873, Lemma A.3, p. 37 (with Fact A.1, p. 29, for the envelope identity).

**Formalization Note** `Φ z = envSupp K (z − z°)`. The first clause is the identity
`(env₁ σ_K)(x) = min_y {σ_K(y) + ½‖x − y‖²}` evaluated at `x = z − z°`, stated with the published
`DualRCD.suppFn` (an `EReal`-valued support function); the second says the max form is attained.
"Convex and `1`-smooth" is `KatyushaNs.IsConvexLSmooth 1 Φ`, `Π_K` is the published
`OrabonaOL.OGD.IsEuclideanProj`, `∂_Y` is coordinate `1` of `gradient`. `z_1 = z° 0`,
`z_2 = z° 1`, and `(p, −q) ∈ K` with `p, q ≥ 0` reads `0 ≤ g 0 ∧ g 1 ≤ 0`. -/
theorem lemma_A_3 (K : Set (EuclideanSpace ℝ (Fin 2))) (hKc : IsCompact K) (hKcv : Convex ℝ K)
    (hK0 : (0 : EuclideanSpace ℝ (Fin 2)) ∈ K) (zo : EuclideanSpace ℝ (Fin 2)) :
    (∀ z, IsLeast {v : EReal | ∃ y, v = DualRCD.suppFn K y + ((‖(z - zo) - y‖ ^ 2 / 2 : ℝ) : EReal)}
        ((envSupp K (z - zo) : ℝ) : EReal)) ∧
    (∀ z, IsGreatest ((fun g => ⟪g, z - zo⟫_ℝ - ‖g‖ ^ 2 / 2) '' K) (envSupp K (z - zo))) ∧
    (∀ z, 0 ≤ envSupp K (z - zo)) ∧
    KatyushaNs.IsConvexLSmooth 1 (fun z => envSupp K (z - zo)) ∧
    (∀ z, OrabonaOL.OGD.IsEuclideanProj K (z - zo) (gradient (fun z => envSupp K (z - zo)) z)) ∧
    ((∀ g ∈ K, 0 ≤ g 0 ∧ g 1 ≤ 0) →
      (∀ z, gradient (fun z => envSupp K (z - zo)) z 1 ≤ 0) ∧
      (∀ θ ℓ : ℝ, 0 < θ → 0 ≤ ℓ → (∀ g ∈ K, -g 1 ≤ g 0 / θ) → 0 ≤ zo 1 →
        ℓ + zo 1 / θ ≤ zo 0 →
        ∀ X Y : ℝ, X ≤ ℓ → 0 ≤ Y → envSupp K (!₂[X, Y] - zo) = 0) ∧
      ((∀ g ∈ K, !₂[g 0, 0] ∈ K) →
        ∀ X Y : ℝ, zo 1 ≤ Y → gradient (fun z => envSupp K (z - zo)) !₂[X, Y] 1 = 0)) := by sorry

end SilverRateSC
