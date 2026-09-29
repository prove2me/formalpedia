-- Prove2me | Theorems.Thm_UnramifiedWhittaker_integral_zetaIntegrand_unipotent_partMeasure_eq_mul_prod_tsum_torusFactor_mul_setIntegral
-- name    : UnramifiedWhittaker.integral_zetaIntegrand_unipotent_partMeasure_eq_mul_prod_tsum_torusFactor_mul_setIntegral
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.683932+00:00
-- url     : https://prove2.me/theorems/c1181e29-a6d0-5c67-bf98-db38a09ab23a
-- title:
--   Unipotent zeta integral: passage from T to S with local factors
-- statement:
--   Let $K$ be a number field, $S \subseteq T$ finite sets of finite places, and $L$ a repetition-free list whose members are exactly the places lying in $T$ but not in $S$. Let $W : \mathrm{GL}_2(\mathbb{A}_K) \to \mathbb{C}$, and for each finite place $v$ let $\varpi_v$ be an element of the valuation ring of $K_v$ whose image in $K_v$ is non-zero, $\lambda_v,\omega_v \in \mathbb{C}$, $I_v$ a finite non-empty index type, $b_{v,i}$ elements of the valuation ring, and $x_v \in K_v$; assume $\varpi_v$ has valuation $\exp(-1)$ for $v \in L$. The hypotheses on $W$ at each $v \in L$ are: $W(\iota_v(n(y))g) = \psi_v(y)W(g)$ for $y \in K_v$, where $n(y) = \begin{pmatrix}1&y\\0&1\end{pmatrix}$ is placed at $v$ and $\psi_v$ is the standard local additive character `StandardAddChar.psiLocal`; right invariance $W(g\,\iota_v(n(r))) = W(g)$ for integral $r$; the Hecke relation $\sum_{i \in I_v} W\bigl(g\,\iota_v\begin{pmatrix}\varpi_v&b_{v,i}\\0&1\end{pmatrix}\bigr) + W\bigl(g\,\iota_v\begin{pmatrix}1&0\\0&\varpi_v\end{pmatrix}\bigr) = \lambda_v W(g)$; and $W(g\,\iota_v(\varpi_v \cdot 1)) = \omega_v W(g)$. Moreover $W(g\,\mathrm{diag}(u,1)) = W(g)$ for every idele unit $u$ with archimedean component $1$, with $u_v = 1$ for all $v \in S$, and with finite part lying in `unitIdeles` (both $u$ and $u^{-1}$ integral at every finite place). Further data: $\chi : \mathbb{A}_K^\times \to \mathbb{C}^\times$, $s \in \mathbb{C}$, and additive Haar measures $\mu_v$ on $K_v$ for the Borel structures. Write $n_v =$ `addCharLevel` $(\psi_v)$, the supremum of the $n \in \mathbb{Z}$ with $\psi_v$ trivial on $\{|y| \le \exp n\}$, $\pi_v$ for the idele which is $\varpi_v$ at $v$ and $1$ elsewhere, and $Z(F) = \int F(\mathrm{diag}(a,1))\chi(a)\|a\|^{s-1}$ for the zeta integrand, $\|\cdot\|$ being the idelic modulus of `distribHaarChar`. Given integrability of the zeta integrand of $g \mapsto W\bigl(g\prod_{v\in L}\iota_v(n(x_v))\bigr)$ against the $T$-part measure $\nu_T$ (the pushforward under `partAt` $T$ of idelic Haar measure restricted to `unitIdelesOutside` $T$), integrability of the zeta integrand of $g \mapsto W\bigl(\mathrm{diag}(\prod_{v\in L}\pi_v^{-n_v},1)\,g\bigr)$ against $\nu_S$, and, for each $v \in L$, absolute summability over $m \in \mathbb{Z}$ of the terms below, the conclusion is $$\int Z\bigl(W(\,\cdot\prod_{v\in L}\iota_v(n(x_v)))\bigr)\,d\nu_T = \Bigl(\int Z\bigl(W(\mathrm{diag}(\textstyle\prod_{v\in L}\pi_v^{-n_v},1)\,\cdot)\bigr)\,d\nu_S\Bigr)\cdot\prod_{v \in L}\sum_{m \in \mathbb{Z}} t_v(m+n_v)\bigl(\chi(\pi_v)\,\mathrm{N}(v)^{1-s}\bigr)^m\frac{\int_{|u|=1}\psi_v(\varpi_v^m x_v u)\,\tilde\chi_v(u)\,d\mu_v(u)}{\mu_v(\{|u|=1\})},$$ where $t_v =$ `torusFactor` $(\#I_v, \lambda_v, \omega_v)$ is the Hecke recursion sequence (value $1$ at $0$, $\lambda_v/\#I_v$ at $1$, and $c_{m+2} = (\lambda_v c_{m+1} - \omega_v c_m)/\#I_v$), extended by $0$ on negative integers, $\mathrm{N}(v)$ is the absolute norm of $v$, and $\tilde\chi_v$ is the local component $\chi \circ \mathrm{localUnit}_v$ of $\chi$ extended by $0$ at $0$. Both products over $L$ are taken in list order.
--
--   This is the unfolding step in the computation of a global zeta integral of a Whittaker-type kernel: the integral over the part of the ideles attached to the larger set $T$ is expressed as the corresponding $S$-integral times, for each place of $T \setminus S$, a local shell series in which the Hecke recursion coefficients are paired with normalised integrals of the additive character over the unit sphere of $K_v$. It is used in the converse-theorem construction of a cusp form, via [`LanglandsTunnell.Converse.CuspSynthesis.exists_isHaarMeasure_torusTransform_eq_of_isJLNice`](thm.html#LanglandsTunnell.Converse.CuspSynthesis.exists_isHaarMeasure_torusTransform_eq_of_isJLNice).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_UnramifiedWhittaker_integral_zetaIntegrand_unipotent_partMeasure_eq_mul_prod_tsum_torusFactor_mul_setIntegral.lean

import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open Matrix MeasureTheory
open IsDedekindDomain NumberField NumberField.AdelicLevel NumberField.AdeleRing NumberField.TateGlobal
open AutomorphicForm AdelicDock

attribute [local instance] NumberField.Idele.ideleBorel in

theorem
UnramifiedWhittaker.integral_zetaIntegrand_unipotent_partMeasure_eq_mul_prod_tsum_torusFactor_mul_setIntegral
    (K : Type) [Field K] [NumberField K]
    (S T : Finset (HeightOneSpectrum (𝓞 K))) (hST : S ⊆ T)
    (L : List (HeightOneSpectrum (𝓞 K))) (hL : L.Nodup) (hLT : ∀ v : HeightOneSpectrum (𝓞 K), v ∈ L ↔ v ∈ T ∧ v ∉ S)
    (W : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ)
    (ϖ : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletionIntegers K)
    (hπ : ∀ v : HeightOneSpectrum (𝓞 K),
      algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) (ϖ v) ≠ 0)
    (hϖ : ∀ v ∈ L, Valued.v (ϖ v : v.adicCompletion K) = WithZero.exp (-1 : ℤ))
    (lam om : HeightOneSpectrum (𝓞 K) → ℂ)
    {I : HeightOneSpectrum (𝓞 K) → Type} [hIf : ∀ v, Fintype (I v)] [hIn : ∀ v, Nonempty (I v)]
    (b : ∀ v : HeightOneSpectrum (𝓞 K), I v → v.adicCompletionIntegers K)
    (hN : ∀ v ∈ L, ∀ (y : v.adicCompletion K) (g : GL (Fin 2) (AdeleRing (𝓞 K) K)),
      W (placeEmbed K v (unipotent y) * g) = StandardAddChar.psiLocal K v y * W g)
    (hK : ∀ v ∈ L, ∀ (r : v.adicCompletionIntegers K) (g : GL (Fin 2) (AdeleRing (𝓞 K) K)),
      W (g * placeEmbed K v (unipotent
        (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) r))) = W g)
    (hU : ∀ u : (AdeleRing (𝓞 K) K)ˣ,
      (u : AdeleRing (𝓞 K) K).1 = 1 →
      (∀ v ∈ S, (u : AdeleRing (𝓞 K) K).2 v = 1) →
      finitePartUnits (𝓞 K) K u ∈ IsDedekindDomain.FiniteAdeleRing.unitIdeles (𝓞 K) K →
      ∀ g : GL (Fin 2) (AdeleRing (𝓞 K) K), W (g * diagOne u) = W g)
    (hT : ∀ v ∈ L, ∀ g : GL (Fin 2) (AdeleRing (𝓞 K) K),
      (∑ i, W (g * placeEmbed K v (repSome
          (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) (ϖ v)) (hπ v)
          (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) (b v i))))) +
        W (g * placeEmbed K v (repInf
          (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) (ϖ v)) (hπ v))) =
        lam v * W g)
    (hZ : ∀ v ∈ L, ∀ g : GL (Fin 2) (AdeleRing (𝓞 K) K),
      W (g * placeEmbed K v (scalarPi
        (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) (ϖ v)) (hπ v))) =
        om v * W g)
    (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (s : ℂ)
    (x : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K)
    [hM : ∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
    [hB : ∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
    (μ : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K))
    [hμ : ∀ v : HeightOneSpectrum (𝓞 K), (μ v).IsAddHaarMeasure]
    (hTint : Integrable
      (zetaIntegrand (fun g => W (g * (L.map fun v => placeEmbed K v (unipotent (x v))).prod)) χ s)
      (NumberField.Idele.productMeasureData K T).νS)
    (hSint : Integrable
      (zetaIntegrand
        (fun g => W (diagOne ((L.map fun v =>
            Units.map (finIncl (𝓞 K) K) (localUnit (𝓞 K) K v (Units.mk0 _ (hπ v)))
              ^ (-(LanglandsTunnell.TateLocal.addCharLevel (StandardAddChar.psiLocal K v)))).prod) * g)) χ s)
      (NumberField.Idele.productMeasureData K S).νS)
    (hsum : ∀ v ∈ L, Summable fun m : ℤ =>
      ‖torusFactor (Fintype.card (I v)) (lam v) (om v)
          (m + LanglandsTunnell.TateLocal.addCharLevel (StandardAddChar.psiLocal K v))
        * ((((χ (Units.map (finIncl (𝓞 K) K) (localUnit (𝓞 K) K v (Units.mk0 _ (hπ v)))) : ℂˣ) : ℂ)
              * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (1 - s)) ^ m)
        * ((∫ u in {u : v.adicCompletion K | Valued.v u = 1},
                StandardAddChar.psiLocal K v
                    (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) (ϖ v) ^ m * x v * u)
                  * LanglandsTunnell.TateLocal.charExt (localChar χ v) u ∂(μ v))
              / (((μ v).real {u : v.adicCompletion K | Valued.v u = 1} : ℝ) : ℂ))‖) :
    (∫ a, zetaIntegrand (fun g => W (g * (L.map fun v => placeEmbed K v (unipotent (x v))).prod)) χ s a
        ∂(NumberField.Idele.productMeasureData K T).νS)
      = (∫ a,
          zetaIntegrand
            (fun g => W (diagOne ((L.map fun v =>
                Units.map (finIncl (𝓞 K) K) (localUnit (𝓞 K) K v (Units.mk0 _ (hπ v)))
                  ^ (-(LanglandsTunnell.TateLocal.addCharLevel (StandardAddChar.psiLocal K v)))).prod) * g)) χ s a
            ∂(NumberField.Idele.productMeasureData K S).νS)
        * (L.map fun v => ∑' m : ℤ,
            torusFactor (Fintype.card (I v)) (lam v) (om v)
                (m + LanglandsTunnell.TateLocal.addCharLevel (StandardAddChar.psiLocal K v))
              * ((((χ (Units.map (finIncl (𝓞 K) K) (localUnit (𝓞 K) K v (Units.mk0 _ (hπ v)))) : ℂˣ) : ℂ)
                    * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (1 - s)) ^ m)
              * ((∫ u in {u : v.adicCompletion K | Valued.v u = 1},
                      StandardAddChar.psiLocal K v
                          (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) (ϖ v) ^ m * x v * u)
                        * LanglandsTunnell.TateLocal.charExt (localChar χ v) u ∂(μ v))
                    / (((μ v).real {u : v.adicCompletion K | Valued.v u = 1} : ℝ) : ℂ))).prod := by sorry
