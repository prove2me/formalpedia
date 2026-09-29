-- Prove2me | Theorems.Thm_UnramifiedWhittaker_eq_of_forall_unipotent_of_localLevelOne_of_scalarPi_of_diagZ
-- name    : UnramifiedWhittaker.eq_of_forall_unipotent_of_localLevelOne_of_scalarPi_of_diagZ
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.683932+00:00
-- url     : https://prove2.me/theorems/ca3abd37-b68b-5d50-b074-e0a50fbc7ce6
-- title:
--   Uniqueness of unramified Whittaker functions on GL₂(ℚᵥ)
-- statement:
--   Let $v$ be a height-one prime of the ring of integers $\mathcal{O}_{\mathbb{Q}}$ of $\mathbb{Q}$, and let $\varpi$ be an element of the valuation ring $\mathcal{O}_v$ of the completion $\mathbb{Q}_v$ whose image in $\mathbb{Q}_v$ is nonzero (hypothesis `hπ`) and has valuation $\mathrm{exp}(-1)$ in the value group written multiplicatively (hypothesis `hϖ`), so that $\varpi$ is a normalised uniformiser. Let $\theta : \mathbb{Q}_v \to \mathbb{C}$ be an arbitrary function, $z \in \mathbb{C}$ a scalar, $t : \mathbb{Z} \to \mathbb{C}$ an arbitrary function, and let $W, W' : \mathrm{GL}_2(\mathbb{Q}_v) \to \mathbb{C}$ be two functions, each assumed to satisfy the same four conditions: (i) $W(n(x)g) = \theta(x)\,W(g)$ for all $x \in \mathbb{Q}_v$ and all $g$, where $n(x)$ is the unipotent matrix $\begin{pmatrix}1&x\\0&1\end{pmatrix}$; (ii) $W(gk) = W(g)$ for all $g$ and all $k$ in the subgroup [`AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤`](def/AdelicDock_LocalEmbedding.html#L178), that is, the preimage under the embedding of $\mathrm{GL}_2(\mathbb{Q}_v)$ into $\mathrm{GL}_2$ of the finite adele ring at the place $v$ of the group of finite adelic matrices $g$ such that both $g$ and $g^{-1}$ satisfy the level-one condition `IsLevelOneMatrix` for the unit ideal; (iii) $W(g \cdot \varpi I_2) = z\,W(g)$ for all $g$, where $\varpi I_2$ is the scalar matrix $\begin{pmatrix}\varpi&0\\0&\varpi\end{pmatrix}$; and (iv) $W\!\left(\begin{pmatrix}\varpi^m&0\\0&1\end{pmatrix}\right) = t(m)$ for every $m \in \mathbb{Z}$. The conclusion is that $W = W'$ as functions on $\mathrm{GL}_2(\mathbb{Q}_v)$.
--
--   This is the uniqueness half of the theory of unramified (spherical) Whittaker functions on $\mathrm{GL}_2$ over a non-archimedean local field: a function with a prescribed additive character behaviour on the unipotent radical, prescribed behaviour under the maximal compact subgroup and under the centre, and prescribed values on the torus elements $\mathrm{diag}(\varpi^m,1)$, is determined by those data, via the Iwasawa decomposition. It is used in the construction of the local Rankin–Selberg data for $\mathrm{GL}_3 \times \mathrm{GL}_2$, being cited by the existence statements for primal and dual middle data with the prescribed local integral identity.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_UnramifiedWhittaker_eq_of_forall_unipotent_of_localLevelOne_of_scalarPi_of_diagZ.lean

import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.RankinSelberg MeasureTheory
  LanglandsTunnell.TateLocal NumberField.TateGlobal UnramifiedWhittaker

theorem UnramifiedWhittaker.eq_of_forall_unipotent_of_localLevelOne_of_scalarPi_of_diagZ
    (v : HeightOneSpectrum (𝓞 ℚ))
    {ϖ : v.adicCompletionIntegers ℚ}
    (hπ : algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ ≠ 0)
    (hϖ : Valued.v (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) = WithZero.exp (-1 : ℤ))
    (θ : v.adicCompletion ℚ → ℂ) (z : ℂ) (t : ℤ → ℂ)
    (W W' : GL (Fin 2) (v.adicCompletion ℚ) → ℂ)
    (hWψ : ∀ (x : v.adicCompletion ℚ) (g : GL (Fin 2) (v.adicCompletion ℚ)), W (unipotent x * g) = θ x * W g)
    (hWK : ∀ (k g : GL (Fin 2) (v.adicCompletion ℚ)),
      k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤ → W (g * k) = W g)
    (hWZ : ∀ g : GL (Fin 2) (v.adicCompletion ℚ),
      W (g * scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) = z * W g)
    (hWT : ∀ m : ℤ, W (diagZ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ m) = t m)
    (hW'ψ : ∀ (x : v.adicCompletion ℚ) (g : GL (Fin 2) (v.adicCompletion ℚ)), W' (unipotent x * g) = θ x * W' g)
    (hW'K : ∀ (k g : GL (Fin 2) (v.adicCompletion ℚ)),
      k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤ → W' (g * k) = W' g)
    (hW'Z : ∀ g : GL (Fin 2) (v.adicCompletion ℚ),
      W' (g * scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) = z * W' g)
    (hW'T : ∀ m : ℤ, W' (diagZ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ m) = t m) :
    W = W' := by sorry
