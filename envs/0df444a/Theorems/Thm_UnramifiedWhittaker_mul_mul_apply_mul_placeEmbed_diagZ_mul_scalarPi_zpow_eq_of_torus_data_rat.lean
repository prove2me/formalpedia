-- Prove2me | Theorems.Thm_UnramifiedWhittaker_mul_mul_apply_mul_placeEmbed_diagZ_mul_scalarPi_zpow_eq_of_torus_data_rat
-- name    : UnramifiedWhittaker.mul_mul_apply_mul_placeEmbed_diagZ_mul_scalarPi_zpow_eq_of_torus_data_rat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.683932+00:00
-- url     : https://prove2.me/theorems/ee1e5af4-1de0-5932-9bbc-84310a9ed960
-- title:
--   Two-parameter torus law for the product W W'F
-- statement:
--   Let $v$ be a nonzero prime of $\mathcal O_{\mathbb Q}$, let $\varpi$ lie in the valuation ring of the completion $\mathbb Q_v$ with nonzero image $\pi$ in $\mathbb Q_v$, let $I$ be a finite nonempty index type with $\#I =$ `Ideal.absNorm v.asIdeal` and $b : I \to \mathcal O_v$, let $W, W', F : \mathrm{GL}_2(\mathbb A_{\mathbb Q}) \to \mathbb C$, let $\psi,\psi'$ be additive characters of $\mathbb Q_v$ with values in $\mathbb C$, and let $\lambda,\omega,\lambda',\omega' \in \mathbb C$. Assume: $\psi$ and $\psi'$ are trivial on the image of $\mathcal O_v$ and each is nontrivial at some $r/\pi$ with $r \in \mathcal O_v$; $W$ (resp. $W'$) transforms on the left under $\bigl(\begin{smallmatrix}1&x\\0&1\end{smallmatrix}\bigr)$ placed at $v$ by $\psi(x)$ (resp. $\psi'(x)$), for all $x \in \mathbb Q_v$; both are right invariant under the same unipotents with entry in $\mathcal O_v$; $\sum_{i} W\bigl(g\,\bigl(\begin{smallmatrix}\pi&b_i\\0&1\end{smallmatrix}\bigr)_v\bigr) + W\bigl(g\,\bigl(\begin{smallmatrix}1&0\\0&\pi\end{smallmatrix}\bigr)_v\bigr) = \lambda\,W(g)$ for all $g$, and likewise for $W'$ with $\lambda'$; $W(g\,(\pi\cdot 1)_v) = \omega\,W(g)$ and $W'(g\,(\pi\cdot 1)_v) = \omega'\,W'(g)$, with $\omega,\omega' \neq 0$; and, for every $g$ whose $v$-component (the image of $g$ under the $v$-component map on $\mathrm{GL}_2$ of the finite adeles) is $1$ and all $m,n \in \mathbb Z$, $F\bigl(g\,t_{m,n}\bigr)$ equals $F(g)$ if $0 \le n$ and $0$ otherwise, where $t_{m,n} = \bigl(\begin{smallmatrix}\pi^m&0\\0&1\end{smallmatrix}\bigr)_v (\pi\cdot 1)_v^{\,n}$, all local matrices being placed at $v$. The conclusion: for every such $g$ and all $m,n \in \mathbb Z$, $$W(g\,t_{m,n})\bigl(W'(g\,t_{m,n})F(g\,t_{m,n})\bigr) = c_{m,n}\cdot W(g)\bigl(W'(g)F(g)\bigr),$$ where $c_{m,n} = (\omega\omega')^{n}\,u_{m}\,u'_{m}$ if $0 \le m$ and $0 \le n$ (with $u_m =$ `heckeRecursionSeq` $q\,\lambda\,\omega\,m$, $u'_m =$ `heckeRecursionSeq` $q\,\lambda'\,\omega'\,m$, $q =$ `Ideal.absNorm v.asIdeal`, and exponents read through `Int.toNat`), and $c_{m,n} = 0$ otherwise; here `heckeRecursionSeq` $N\,\lambda\,\omega$ is the sequence with values $1$, $\lambda/N$ and $u_{m+2} = (\lambda u_{m+1} - \omega u_m)/N$.
--
--   This is the local two-parameter torus law at an unramified place for the product of two level-zero Hecke-eigen Whittaker functions with the indicator-type function $F$, the combination that occurs in the Rankin–Selberg integrand; the vanishing for $m < 0$ comes from the Whittaker factors, that for $n < 0$ from $F$. It rests on the one-place torus recursion [`UnramifiedWhittaker.apply_mul_placeEmbed_diagZ_eq_mul_torusFactor`](thm.html#UnramifiedWhittaker.apply_mul_placeEmbed_diagZ_eq_mul_torusFactor) and is used in the construction of Rankin–Selberg test data over $\mathbb Q$ in [`AutomorphicForm.exists_rankinSelberg_testData_of_isArithGenuineCuspRealizable_rat`](thm.html#AutomorphicForm.exists_rankinSelberg_testData_of_isArithGenuineCuspRealizable_rat).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_UnramifiedWhittaker_mul_mul_apply_mul_placeEmbed_diagZ_mul_scalarPi_zpow_eq_of_torus_data_rat.lean

import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_AutomorphicForm_LocalOrbitalBase

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Matrix
open IsDedekindDomain NumberField NumberField.AdelicLevel AdelicDock AutomorphicForm UnramifiedWhittaker

theorem UnramifiedWhittaker.mul_mul_apply_mul_placeEmbed_diagZ_mul_scalarPi_zpow_eq_of_torus_data_rat
    (v : HeightOneSpectrum (𝓞 ℚ))
    {ϖ : v.adicCompletionIntegers ℚ}
    (hπ : algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ ≠ 0)
    {I : Type*} [Fintype I] [Nonempty I] (b : I → v.adicCompletionIntegers ℚ)
    (hI : Fintype.card I = Ideal.absNorm v.asIdeal)
    (W W' F : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ) → ℂ) (ψ ψ' : AddChar (v.adicCompletion ℚ) ℂ) (lam om lam' om' : ℂ)
    (hψ0 : ∀ r : v.adicCompletionIntegers ℚ, ψ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) r) = 1)
    (hψ1 : ∃ r : v.adicCompletionIntegers ℚ,
      ψ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) r /
        algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) ≠ 1)
    (hψ'0 : ∀ r : v.adicCompletionIntegers ℚ, ψ' (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) r) = 1)
    (hψ'1 : ∃ r : v.adicCompletionIntegers ℚ,
      ψ' (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) r /
        algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) ≠ 1)
    (hN : ∀ (x : v.adicCompletion ℚ) (g : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)), W (placeEmbed ℚ v (unipotent x) * g) = ψ x * W g)
    (hN' : ∀ (x : v.adicCompletion ℚ) (g : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)), W' (placeEmbed ℚ v (unipotent x) * g) = ψ' x * W' g)
    (hK : ∀ (r : v.adicCompletionIntegers ℚ) (g : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)),
      W (g * placeEmbed ℚ v (unipotent (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) r))) = W g)
    (hK' : ∀ (r : v.adicCompletionIntegers ℚ) (g : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)),
      W' (g * placeEmbed ℚ v (unipotent (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) r))) = W' g)
    (hT : ∀ g : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ),
      (∑ i, W (g * placeEmbed ℚ v (repSome (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ
          (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (b i))))) +
        W (g * placeEmbed ℚ v (repInf (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ)) = lam * W g)
    (hT' : ∀ g : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ),
      (∑ i, W' (g * placeEmbed ℚ v (repSome (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ
          (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (b i))))) +
        W' (g * placeEmbed ℚ v (repInf (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ)) = lam' * W' g)
    (hZ : ∀ g : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ),
      W (g * placeEmbed ℚ v (scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ)) = om * W g)
    (hZ' : ∀ g : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ),
      W' (g * placeEmbed ℚ v (scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ)) = om' * W' g)
    (hom : om ≠ 0) (hom' : om' ≠ 0)
    (hF : ∀ (g : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) (m n : ℤ), localAt ℚ v g = 1 →
      F (g * placeEmbed ℚ v
          (diagZ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ m *
            scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ n)) =
        (if 0 ≤ n then F g else 0)) :
    ∀ (g : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) (m n : ℤ), localAt ℚ v g = 1 →
      W (g * placeEmbed ℚ v
            (diagZ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ m *
              scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ n)) *
        (W' (g * placeEmbed ℚ v
            (diagZ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ m *
              scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ n)) *
          F (g * placeEmbed ℚ v
            (diagZ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ m *
              scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ n))) =
      (if 0 ≤ m ∧ 0 ≤ n then
          (om * om') ^ n.toNat *
            heckeRecursionSeq ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) lam om m.toNat *
            heckeRecursionSeq ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) lam' om' m.toNat
        else 0) * (W g * (W' g * F g)) := by sorry
