-- Prove2me | Theorems.Thm_TwistedUnipotentTerm_wordIndicator_semiLocalCentral_mul_semiLocalUnipotent_eq_walkCount
-- name    : TwistedUnipotentTerm.wordIndicator_semiLocalCentral_mul_semiLocalUnipotent_eq_walkCount
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.683932+00:00
-- url     : https://prove2.me/theorems/3c92814c-838a-5cdf-aef1-6be563b46afd
-- title:
--   Word indicator at central times unipotent counts tree walks
-- statement:
--   Let $K$ and $L$ be number fields with $L$ a $K$-algebra, let $v$ be a height-one prime of $\mathcal{O}_K$ and $w$ a prime of $\mathcal{O}_L$ lying over $v$ (an element of `v.Extension (𝓞 L)`). Let $\varpi$ be an irreducible element of the valuation ring $\mathcal{O}_w$ of the completion $L_w$ whose image in $L_w$ is non-zero, let $rT : \mathrm{Fin}\,n \to \mathrm{GL}_2(L_w)$ be a Hecke coset system for the subgroup [`LocalGL2.integralSubgroup`](def/LocalLanglands_LocalHeckeInstance.html#L13) (the image of $\mathrm{GL}_2(\mathcal{O}_w)$ in $\mathrm{GL}_2(L_w)$) and the element [`LocalGL2.diagPi`](def/LocalLanglands_HeckeCosetLocal.html#L68) $=\mathrm{diag}(\varpi,1)$, i.e. each $rT\,i$ lies in the double coset $U\,\mathrm{diag}(\varpi,1)\,U$, every element of that double coset lies in $rT\,i\cdot U$ for some $i$, and $i \mapsto rT\,i\cdot U$ is injective; and let $z \in \mathrm{GL}_2(L_w)$ have underlying matrix $\varpi\cdot 1$. Let $W : \mathbb{N}\to\mathbb{N}\to\mathbb{N}$ satisfy $W(0,0)=1$, $W(0,d+1)=0$, $W(k+1,0)=(q+1)W(k,1)$ and $W(k+1,d+1)=W(k,d)+q\,W(k,d+2)$, where $q =$ `Ideal.absNorm w.1.asIdeal`. Fix $k,j \in \mathbb{N}$, a unit $\zeta$ of $L\otimes_K K_v$ and an element $x$ of $L\otimes_K K_v$, and let $h$ be the product of the scalar matrix $\zeta\cdot 1$ (`semiLocalCentral`) with $\begin{pmatrix}1&x\\0&1\end{pmatrix}$ (`semiLocalUnipotent`). Write $N(h)$ for `wordIndicator K L v w n rT z k j h`, the sum over words $\iota : \mathrm{Fin}\,k \to \mathrm{Fin}\,n$ of the indicator (with value $1 \in \mathbb{C}$) of the semi-local integral set of $\mathrm{GL}_2(L\otimes_K K_v)$ evaluated at the semi-local component at $v$ of the adelic embedding at $w$ of $\bigl(\prod_i rT(\iota\,i)\bigr)z^j$, inverted and multiplied by $h$. Denote by $\zeta_{w'}$ and $x_{w'}$ the components of $\zeta$ and $x$ under the base-change isomorphism $L\otimes_K K_v \cong \prod_{w'\mid v} L_{w'}$. The conclusion is a conjunction of two implications: first, if $N(h) \neq 0$ then $|\zeta_{w'}|=1$ and $x_{w'} \in \mathcal{O}_{w'}$ for every $w' \neq w$ above $v$, and $|\zeta_w|^2 = |\varpi|^{k+2j}$; second, if those integrality conditions away from $w$ hold and $|\zeta_w|^2 = |\varpi|^{k+2j}$, then $N(h)$ equals the image in $\mathbb{C}$ of $W\bigl(k,\,2\,(\mathrm{log}\,|x_w|)^{+}\bigr)$, the second argument being twice the truncation to $\mathbb{N}$ of `WithZero.log` of the valuation of $x_w$.
--
--   This is the semi-local form, over the product of the completions $L_{w'}$ for $w'\mid v$, of the count of words in the Hecke coset representatives of $U\,\mathrm{diag}(\varpi,1)\,U$ meeting a given coset: away from $w$ the condition is integrality of $\zeta$ and $x$, at $w$ the indicator counts walks of length $k$ in the $(q+1)$-regular Bruhat–Tits tree of $\mathrm{PGL}_2(L_w)$ ending at distance $2r$, where $q^{r} = \max(1,|x_w|)$, with the parity constraint $2\,\mathrm{ord}_w(\zeta_w) = k+2j$ acting as a gate. It specialises the purely local count [`LocalGL2.sum_indicator_word_inv_mul_scalar_mul_unipotentGL2_mem_localIntegralSet_eq_walkCount`](thm.html#LocalGL2.sum_indicator_word_inv_mul_scalar_mul_unipotentGL2_mem_localIntegralSet_eq_walkCount), and is used in the analysis of the twisted unipotent orbital function, both for its factorisation through the walk counts and for its local constancy and compact support.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_TwistedUnipotentTerm_wordIndicator_semiLocalCentral_mul_semiLocalUnipotent_eq_walkCount.lean

import Definitions.Def_TwistedUnipotentTerm_SemiLocalOrbitalVocab
import Definitions.Def_LocalLanglands_HeckeCosetLocal

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped TensorProduct

theorem TwistedUnipotentTerm.wordIndicator_semiLocalCentral_mul_semiLocalUnipotent_eq_walkCount
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) (w : v.Extension (𝓞 L))
    (ϖ : w.1.adicCompletionIntegers L) (hϖ : Irreducible ϖ)
    (hϖ0 : algebraMap (w.1.adicCompletionIntegers L) (w.1.adicCompletion L) ϖ ≠ 0)
    (n : ℕ) (rT : Fin n → GL (Fin 2) (w.1.adicCompletion L))
    (hrT : HeckeIntegralSeam.IsHeckeCosetSystem
      (LocalGL2.integralSubgroup (w.1.adicCompletionIntegers L) (w.1.adicCompletion L))
      (LocalGL2.diagPi ϖ hϖ0) rT)
    (z : GL (Fin 2) (w.1.adicCompletion L))
    (hz : (z : Matrix (Fin 2) (Fin 2) (w.1.adicCompletion L)) =
      algebraMap (w.1.adicCompletionIntegers L) (w.1.adicCompletion L) ϖ •
        (1 : Matrix (Fin 2) (Fin 2) (w.1.adicCompletion L)))
    (W : ℕ → ℕ → ℕ) (h00 : W 0 0 = 1) (h0s : ∀ d : ℕ, W 0 (d + 1) = 0)
    (hroot : ∀ k : ℕ, W (k + 1) 0 = (Ideal.absNorm w.1.asIdeal + 1) * W k 1)
    (hstep : ∀ k d : ℕ, W (k + 1) (d + 1) = W k d + Ideal.absNorm w.1.asIdeal * W k (d + 2))
    (k j : ℕ) (ζ : (L ⊗[K] v.adicCompletion K)ˣ) (x : L ⊗[K] v.adicCompletion K) :
    (TwistedUnipotentTerm.wordIndicator K L v w n rT z k j
          (TwistedUnipotentTerm.semiLocalCentral K L v ζ * TwistedUnipotentTerm.semiLocalUnipotent K L v x) ≠ 0 →
        (∀ w' : v.Extension (𝓞 L), w' ≠ w →
            Valued.v ((TwistedUnipotentTerm.semiLocalUnitComponent K L v w' ζ : (w'.1.adicCompletion L)ˣ) :
                w'.1.adicCompletion L) = 1 ∧
              HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v x w' ∈
                w'.1.adicCompletionIntegers L) ∧
          Valued.v ((TwistedUnipotentTerm.semiLocalUnitComponent K L v w ζ : (w.1.adicCompletion L)ˣ) :
              w.1.adicCompletion L) ^ 2 =
            Valued.v (algebraMap (w.1.adicCompletionIntegers L) (w.1.adicCompletion L) ϖ) ^ (k + 2 * j)) ∧
      ((∀ w' : v.Extension (𝓞 L), w' ≠ w →
          Valued.v ((TwistedUnipotentTerm.semiLocalUnitComponent K L v w' ζ : (w'.1.adicCompletion L)ˣ) :
              w'.1.adicCompletion L) = 1 ∧
            HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v x w' ∈
              w'.1.adicCompletionIntegers L) →
        Valued.v ((TwistedUnipotentTerm.semiLocalUnitComponent K L v w ζ : (w.1.adicCompletion L)ˣ) :
            w.1.adicCompletion L) ^ 2 =
          Valued.v (algebraMap (w.1.adicCompletionIntegers L) (w.1.adicCompletion L) ϖ) ^ (k + 2 * j) →
        TwistedUnipotentTerm.wordIndicator K L v w n rT z k j
            (TwistedUnipotentTerm.semiLocalCentral K L v ζ * TwistedUnipotentTerm.semiLocalUnipotent K L v x) =
          (W k (2 * (WithZero.log (Valued.v
            (HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v x w))).toNat) : ℂ)) := by sorry
