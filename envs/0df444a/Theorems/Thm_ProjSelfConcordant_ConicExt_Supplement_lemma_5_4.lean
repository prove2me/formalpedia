-- Prove2me | Theorems.Thm_ProjSelfConcordant_ConicExt_Supplement_lemma_5_4
-- name    : ProjSelfConcordant.ConicExt.Supplement.lemma_5_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T11:25:52.377576+00:00
-- url     : https://prove2.me/theorems/b7322aed-2a17-49f3-9410-2fc9a3a542ac
-- title:
--   Lemma 5.4, p. 13 — the duality map is a bijection onto dom f∗ taking G to G∗ and C to −C∗
-- statement:
--   Let $X\subset\mathbb R^n$ be a regular convex set with interior $X^o$ and $f$ a projectively self-concordant barrier on $X$ with parameter $\gamma$. Let $f_*$ be the dual function of Definition 5.2, with domain of definition $\operatorname{dom}f_*$, and let
--   $$P(x)=-\frac{f'(x)}{1+\langle f'(x),x\rangle}.$$
--   Write $G=f''-f'f'^T$ and $C_{ijk}=f'''_{ijk}-2f''_{ij}f'_k-2f''_{ik}f'_j-2f''_{jk}f'_i+4f'_if'_jf'_k$ for the affine metric and cubic form of $f$, and $G_*$, $C_*$ for those of $f_*$. Then
--
--   1. $P$ is a bijection from $\{x\in X^o\mid 1+\langle f'(x),x\rangle>0\}$ onto $\operatorname{dom}f_*$;
--   2. $P$ takes $G$ to $G_*$: for every such $x$ and all directions $u,v$, with $DP(x)$ the differential of $P$,
--   $$G_*(P(x))[DP(x)u,DP(x)v]=G(x)[u,v];$$
--   3. consequently $G_*(p)$ is positive definite for every $p\in\operatorname{dom}f_*$;
--   4. $P$ takes $C$ to $-C_*$: for every such $x$ and all $u,v,w$,
--   $$C_*(P(x))[DP(x)u,DP(x)v,DP(x)w]=-C(x)[u,v,w].$$
--
--   The lemma says the duality map behaves like the Legendre–Fenchel map, exchanging the cubic form for its negative; it is the main step towards Corollary 5.5.
--
--   **Formalization Note** "Takes the form $A$ to the form $B$" is the transport identity of the proof on pp. 14–15, $(\partial p/\partial x)^T B\,(\partial p/\partial x)=A$ and its trilinear analogue, written with the Fréchet derivative of $P$. $f'(x)$ is `gradient f x`; derivatives of $f_*$ are taken of the total function $f_*$ at points of its domain.
--
--   Differences from the source:
--   - encoding: f : Xᵒ → ℝ and f∗ on its domain → total functions; derivatives of f∗ are read at points of dom f∗; reason: only values near these points enter the statement
--   - encoding: functions and derivatives on open subsets of ℝⁿ → total functions on EuclideanSpace ℝ (Fin n), with Fréchet derivatives evaluated on the stated open domains; reason: every source function extends outside its domain; derivatives at interior points depend only on local values, and the Euclidean inner product identifies covectors with gradients when needed
-- source:
--   Hildebrand, Projectively Self-Concordant Barriers, arXiv:1909.01883v2, p. 13, Lemma 5.4 (proof pp. 13–15)

import Mathlib
import Definitions.Def_ProjSelfConcordant_ConicExt_Setting
import Definitions.Def_ProjSelfConcordant_ConicExt_Supplement_Barrier
import Definitions.Def_ProjSelfConcordant_ConicExt_Supplement_Duality

namespace ProjSelfConcordant.ConicExt.Supplement

/-- Lemma 5.4, p. 13: for a projectively self-concordant barrier `f` with parameter `γ` on a
regular convex set `X`, the map `P(x) = −f′(x)/(1 + ⟨f′(x), x⟩)` is a bijection from
`{x ∈ Xᵒ | 1 + ⟨f′(x), x⟩ > 0}` onto the domain of definition of `f∗`; through its differential it
takes the affine metric `G = f″ − f′f′ᵀ` of `f` to the affine metric `G∗` of `f∗`, which is
therefore positive definite on the domain of `f∗`, and it takes the cubic form `C` of `f` to
`−C∗`, the negative of the cubic form of `f∗`. -/
theorem lemma_5_4 {n : ℕ} (X : Set (EuclideanSpace ℝ (Fin n)))
    (hX : RegularConvexSet X) (γ : ℝ) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ProjBarrier γ X f) :
    Set.BijOn (projGrad f) (admissibleSet X f) (dualDomain X f) ∧
    (∀ x ∈ admissibleSet X f, ∀ u v : EuclideanSpace ℝ (Fin n),
      affMetric (fstar X f) (projGrad f x)
          (fderiv ℝ (projGrad f) x u) (fderiv ℝ (projGrad f) x v)
        = affMetric f x u v) ∧
    (∀ p ∈ dualDomain X f, ∀ h : EuclideanSpace ℝ (Fin n), h ≠ 0 →
      0 < affMetric (fstar X f) p h h) ∧
    (∀ x ∈ admissibleSet X f, ∀ u v w : EuclideanSpace ℝ (Fin n),
      cubicForm (fstar X f) (projGrad f x)
          (fderiv ℝ (projGrad f) x u) (fderiv ℝ (projGrad f) x v)
          (fderiv ℝ (projGrad f) x w)
        = -cubicForm f x u v w) := by sorry

end ProjSelfConcordant.ConicExt.Supplement
